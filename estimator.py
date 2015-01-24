# -*- coding: utf-8 -*-
"""
Complexity estimates for solving LWE.

.. moduleauthor:: Martin R. Albrecht <martinralbrecht@googlemail.com>

"""

from collections import OrderedDict

from sage.modules.all import vector
from sage.functions.log import exp, log
from sage.functions.other import ceil, sqrt, floor, binomial
from sage.interfaces.magma import magma
from sage.matrix.all import Matrix
from sage.misc.all import cached_function
from sage.misc.misc import get_verbose, srange, prod
from sage.rings.all import QQ, RR, ZZ, RealField, PowerSeriesRing
from sage.symbolic.all import pi, e

from sage.crypto.lwe import Regev, LindnerPeikert

from sage.misc.cachefunc import cached_method

# config

tau_default = 0.2
tau_prob_default = 0.1

# utility functions #


def cost_str(d, keyword_width=None):
    """
    Return string of key,value pairs as a string "key0: value0, key1: value1"

    :param d:        report dictionary
    :keyword_width:  keys are printed with this width

    EXAMPLE:

    By default dicts are unordered, hence the order of the output of this function is undefined::

        sage: s = {u"δ":5, "bar":2}
        sage: print cost_str(s)
        bar:         2,  5:         δ

    Use `OrderedDict` if you require ordered output::

        sage: s = OrderedDict([(u"δ", 5), ("bar",2)]) #
        sage: print cost_str(s)
        δ:         5,  bar:         2

    """
    if d is None:
        return
    s = []
    for k in d:
        v = d[k]
        if keyword_width:
            fmt = u"%%%ds" % keyword_width
            k = fmt % k
        if ZZ(1)/2048 < v < 2048 or v == 0:
            try:
                s.append(u"%s: %9d" % (k, ZZ(v)))
            except TypeError:
                if v < 2.0 and v >= 0.0:
                    s.append(u"%s: %9.7f" % (k, v))
                else:
                    s.append(u"%s: %9.4f" % (k, v))
        else:
            t = u"≈2^%.1f" % log(v, 2).n()
            s.append(u"%s: %9s" % (k, t))
    return u",  ".join(s)


def cost_reorder(d, ordering):
    """
    Return a new ordered dict from the key:value pairs in `d` but reordered such that the keys in
    ordering come first.

    :param d:        input dictionary
    :param ordering: keys which should come first (in order)


    EXAMPLE::

        sage: d = OrderedDict([("a",1),("b",2),("c",3)]); d
        OrderedDict([('a', 1), ('b', 2), ('c', 3)])

        sage: cost_reorder(d, ["b","c","a"])
        OrderedDict([('b', 2), ('c', 3), ('a', 1)])

    """
    keys = list(d)
    for key in ordering:
        keys.pop(keys.index(key))
    keys = list(ordering) + keys
    r = OrderedDict()
    for key in keys:
        r[key] = d[key]
    return r


def cost_repeat(d, times):
    """
    Return a report with all costs multiplied by `times`.

    :param d: a report object
    :param times: the number of times it should be run
    :returns: a new report

    We maintain a local dictionary which decides if an entry is multiplied by `times` or not.
    For example, δ would not be multiplied but "\#bop" would be. This check is strict such that
    unknown entries raise an error. This is to enforce a decision  on whether an entry should be
    multiplied by `times` if the function `report` reports on is called `times` often.

    EXAMPLE::

        sage: n, alpha, q = unpack_lwe(Regev(128))
        sage: print cost_str(cost_repeat(sis(n, alpha, q), 2^10))
        bkz2:   ≈2^77.0,  #calls:   ≈2^30.5,  δ_0: 1.0093614,  k:        98,  ...
        sage: print cost_str(cost_repeat(sis(n, alpha, q), 1))
        bkz2:   ≈2^67.0,  #calls:   ≈2^20.5,  δ_0: 1.0093614,  k:        98,  ...

    """

    do_repeat = {
        u"bop": True,
        u"rop": True,
        u"oracle": True,
        u"bkz2": True,
        u"lp": True,
        u"ds": True,
        u"fplll": True,
        u"sieve": True,
        u"enum": True,
        u"enumop": True,

        u"mem": False,
        u"δ_0": False,
        u"k": False,
        u"ε": False,
        u"D_reg": False,
        u"t": False,
        u"Pr[⊥]": False,  # we are leaving probabilities alone
        u"m": False,
    }

    ret = OrderedDict()
    for key in d:
        try:
            if do_repeat[key]:
                ret[key] = times * d[key]
            else:
                ret[key] = d[key]
        except KeyError:
            raise NotImplemented(u"You found a bug, this function does not know about '%s' but should."%key)
    ret[u"repeat"] = times
    return ret


def stddevf(sigma):
    """
    σ → std deviation

    :param sigma: Gaussian width parameter σ

    EXAMPLE::

        sage: n = 64.0
        sage: stddevf(n)
        25.532...
    """
    return sigma/sqrt(2*pi).n()


def sigmaf(stddev):
    """
    std deviation → σ

    :param sigma: standard deviation

    EXAMPLE::

        sage: n = 64.0
        sage: sigmaf(stddevf(n))
        64.000...
    """
    return sqrt(2*pi).n()*stddev


def alphaf(sigma, q, sigma_is_stddev=False):
    """
    σ, q → α

    :param sigma: Gaussian width parameter (or standard deviation if `sigma_is_stddev` is `True`)
    :param q: modulus
    :param sigma_is_stddev: if `True` then `sigma` is interpreted as the standard deviation
    :returns: α = σ/q or σ·sqrt(2π)/q depending on `sigma_is_stddev`
    :rtype: real number

    """
    if sigma_is_stddev is False:
        return RR(sigma/q)
    else:
        return RR(sigmaf(sigma)/q)


def uniform_variance_from_bounds(a, b):
    """
    Variance for uniform distribution from bounds.

    :param a:
    :param b:
    :returns:
    :rtype:

    """
    n = b - a + 1
    return (n**2 - 1)/ZZ(12)


def unpack_lwe(lwe):
    """
    Return n, α, q given an LWE instance object.

    :param lwe: LWE object
    :returns: n, α, q
    :rtype: tuple

    """
    n = lwe.n
    q = lwe.K.order()
    try:
        alpha = alphaf(sigmaf(lwe.D.sigma), q)
    except AttributeError:
        # older versions of Sage use stddev, not sigma
        alpha = alphaf(sigmaf(lwe.D.stddev), q)
    return n, alpha, q


def preprocess_params(n, alpha, q, success_probability=None, prec=None):
    """
    Check if parameters n, α, q are sound and return correct types.
    """
    if n < 1:
        raise ValueError("LWE dimension must be greater than 0.")
    if alpha >= 1.0 or alpha <= 0.0:
        raise ValueError("Fraction of noise must be between 0 and 1.")
    if q < 1:
        raise ValueError("LWE modulus must be greater than 0.")
    if prec is None:
        prec = 128
    RR = RealField(prec)
    n, alpha, q =  ZZ(n), RR(alpha), ZZ(q),

    if success_probability is not None:
        if success_probability >= 1.0 or success_probability <= 0.0:
            raise ValueError("success_probability must be between 0 and 1.")
        return n, alpha, q, RR(success_probability)
    else:
        return n, alpha, q


################################
# Section 2                    #
################################


def switch_modulus(n, alpha, q, s_variance):
    """
    Return modulus switched parameters.

    :param n:        the number of variables in the LWE instance
    :param alpha:    noise size
    :param q:        modulus
    :param s_var:    the variance of the secret


    EXAMPLE::

       sage: switch_modulus(128, 0.01, 65537, uniform_variance_from_bounds(0,1))
       (128, 0.0141421356237310, 410.000000000000)

       sage: switch_modulus(128, 0.001, 65537, uniform_variance_from_bounds(0,1))
       (128, 0.00141421356237310, 4094.00000000000)

       sage: switch_modulus(128, 0.001, 65537, uniform_variance_from_bounds(-5,5))
       (128, 0.00141421356237310, 25889.0000000000)

    """
    p = RR(ceil(sqrt(2*pi*s_variance*n/ZZ(12)) / alpha))
    beta = RR(sqrt(2)*alpha)
    return n, beta, p


################################
# Section 3: Lattice Reduction #
################################


def k_chen(delta):
    """
    Estimate required blocksize `k` for a given root-hermite factor δ based on [PhD:Chen13]_

    :param delta: root-hermite factor

    EXAMPLE::

        sage: 50 == k_chen(1.0121)
        True
        sage: 100 = k_chen(1.0093)
        True
        sage: k_chen(1.0024) # Chen reports 800
        808

    .. [PhD:Chen13] Yuanmi Chen. Réduction de réseau et sécurité concrète du chiffrement
                    complètement homomorphe. PhD thesis, Paris 7, 2013.
    """
    k = ZZ(40)
    RR = delta.parent()
    pi_r = RR(pi)
    e_r = RR(e)

    f = lambda k: (k/(2*pi_r*e_r) * (pi_r*k)**(1/k))**(1/(2*(k-1)))

    while f(2*k) > delta:
        k *= 2
    while f(k+10) > delta:
        k += 10
    while True:
        if f(k) < delta:
            break
        k += 1

    return k


def bkz_runtime_delta_DS(delta, n):
    """
    Runtime estimation assuming the δ² model.
    """
    return RR(0.009/log(delta, 2)**2 - 27 + log(2.3*10**9, 2))


def bkz_runtime_delta_LP(delta, n):
    """
    Runtime estimation assuming the Lindner-Peikert model.
    """
    return RR(1.8/log(delta, 2) - 110 + log(2.3*10**9, 2))


def bkz_runtime_k_sieve(k, n):
    """
    Runtime estimation given `k` and assuming sieving is used to realise the SVP oracle.
    """
    return RR(0.3774*k + 20  + 3*log(n, 2) - 2*log(k, 2) + log(log(n, 2), 2))


def bkz_runtime_k_bkz2(k, n):
    """
    Runtime estimation given `k` and assuming [AC:CheNgu11]_ estimates are correct.

    The constants in this function were derived as follows based on Table 3 in [AC:CheNgu11]_::

        sage: dim = [100, 110, 120, 130, 140, 150, 160, 170, 180, 190, 200, 250]
        sage: nodes = [40.8, 45.3, 50.3, 56.3, 63.3, 69.4, 79.9, 89.1, 99.1, 103.3, 111.1, 175.2]
        sage: times = [c + log(200,2).n() for c in nodes]
        sage: T = zip(dim, nodes)
        sage: var("a,b,c,k")
        sage: f = a*k^2 + b*k + c
        sage: f = f.function(k)
        sage: f.subs(find_fit(T, f, solution_dict=True))
        k |--> 0.002897773577138274*k^2 - 0.1226624805533656*k + 31.4749723637768

    .. [AC:CheNgu11] Yuanmi Chen and Phong Q. Nguyen. BKZ 2.0: Better lattice security estimates. In
                     Dong Hoon Lee and Xiaoyun Wang, editors, ASIACRYPT 2011, volume 7073 of LNCS,
                     pages 1–20. Springer, December 2011.


    """
    repeat = 3*log(n, 2) - 2*log(k, 2) + log(log(n, 2), 2)
    return RR(0.002897773577138052*k**2 - 0.12266248055336093*k + 23.831116173986075 + repeat)


def bkz_runtime_delta_bkz2(delta, n):
    """
    Runtime estimation extrapolated from BKZ 2.0 timings.
    """
    k = k_chen(delta)
    return bkz_runtime_k_bkz2(k, n)


def bkz_runtime_k_fplll(k, n):
    """
    Runtime estimation extrapolated from fpLLL 4.0.4 experiments
    """
    repeat = 3*log(n, 2) - 2*log(k, 2) + log(log(n, 2), 2)
    return RR(0.013487467331762426*k**2 - 0.28245244492771304*k + 21.017892848466957 + repeat)


def bkz_runtime_delta(delta, n, log_repeat=0):
    """
    Runtime estimates for BKZ (2.0) given δ and n
    """
    # t_lp = bkz_runtime_delta_LP(delta, n) + log_repeat
    # t_ds = bkz_runtime_delta_DS(delta, n) + log_repeat

    RR = delta.parent()

    k = k_chen(delta)
    t_sieve = RR(bkz_runtime_k_sieve(k, n) + log_repeat)
    t_bkz2  = RR(bkz_runtime_k_bkz2(k, n)  + log_repeat)
    t_fplll = RR(bkz_runtime_k_fplll(k, n) + log_repeat)

    r = OrderedDict([(u"δ_0", delta),
                     (u"bkz2", RR(2)**t_bkz2),
                     (u"k", k),
                     # (u"lp", RR(2)**t_lp),
                     # (u"ds", RR(2)**t_ds),
                     (u"fplll", RR(2)**t_fplll),
                     (u"sieve", RR(2)**t_sieve)])

    return r


def lattice_redution_opt_m(n, q, delta):
    return ZZ(round(sqrt(n*log(q, 2)/log(delta, 2))))


def mitm(n, alpha, q, success_probability=0.99, secret_bounds=None):
    """
    Return meet-in-the-middle estimates.

    :param n: dimension
    :param alpha: noise parameter
    :param q: modulus
    :param success_probability: desired success probability
    :param secret_bounds: tuple with lower and upper bound on the secret
    :returns: report
    :rtype: OrderedDict

    """
    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)
    ret = OrderedDict()
    RR = alpha.parent()
    if secret_bounds is None:
        ret["rop"] = RR((alpha*q)**(n/2) * 2*n)
        ret["mem"] = RR((alpha*q)**(n/2) * 2*n)
    else:
        a, b = secret_bounds
        ret["rop"] = RR((b-a+1)**(n/2) * 2*n)
        ret["mem"] = RR((b-a+1)**(n/2))
    ret["bop"] = RR(log(q, 2) * ret["rop"])
    ret["oracle"] = 2*n
    return cost_reorder(ret, ["bop", "oracle", "mem"])

####################
# Section 5.2: BKW #
####################


@cached_method
def bkw_required_m(sigma, q, success_probability, other_sigma=None):
    RR = sigma.parent()
    if other_sigma is not None:
        sigma = RR(sqrt(sigma**2 + other_sigma**2))
    adv = RR(exp(-RR(pi)*(RR(sigma/q)**2)))
    return RR(success_probability)/RR(adv)


def bkw(n, alpha, q, success_probability=0.99, optimisation_target="bop", prec=None):
    """

    :param n:                    dimension > 0
    :param alpha:                size of the noise α < 1.0
    :param q:                    modulus > 0
    :param success_probability:  probability of success < 1.0
    :param optimisation_target:  field to use to decide if parameters are better
    :param prec:                 precision used for floating point computations

    """
    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)
    sigma = alpha*q

    RR = alpha.parent()

    best = None
    t = RR(2*(log(q, 2) - log(sigma, 2))/log(n, 2))
    while True:
        a = RR(t*log(n, 2))  # target number of adds: a = t*log_2(n)
        b = RR(n/a)  # window width
        sigma_final = RR(n**t).sqrt() * sigma  # after n^t adds we get this σ

        m = bkw_required_m(sigma_final, q, success_probability)

        tmp = a*(a-1)/2 * (n+1) - b*a*(a-1)/4 - b/6 * RR((a-1)**3 + 3/2*(a-1)**2 + (a-1)/2)
        stage1a = RR(q**b-1)/2 * tmp
        stage1b = m * (a/2 * (n + 2))
        stage1  = stage1a + stage1b

        nrops = RR(stage1)
        nbops = RR(log(q, 2) * nrops)
        ncalls = RR(a * ceil(RR(q**b)/RR(2)) + m)
        nmem = ceil(RR(q**b)/2) * a * (n + 1 - b * (a-1)/2)

        current = OrderedDict([(u"t", t),
                               (u"bop", nbops),
                               (u"oracle", ncalls),
                               (u"m", m),
                               (u"mem", nmem),
                               (u"rop", nrops)])

        if optimisation_target != u"oracle":
            current = cost_reorder(current, (optimisation_target, u"oracle", u"t"))
        else:
            current = cost_reorder(current, (optimisation_target, u"t"))

        if get_verbose() >= 2:
            print cost_str(current)

        if not best:
            best = current
        else:
            if best[optimisation_target] > current[optimisation_target]:
                best = current
            else:
                break
        t += 0.05
    return best


#######################################################
# Section 5.3: Using Lattice Reduction To Distinguish #
#######################################################


def sis(n, alpha, q, log_eps=None,
        success_probability=0.99, optimisation_target=u"bkz2"):

    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)
    f = lambda eps: RR(sqrt(log(1/eps)/pi))
    RR = alpha.parent()

    best = None
    if log_eps is None:
        for log_eps in range(1, n):
            current = sis(n, alpha, q, log_eps=-log_eps,
                          optimisation_target=optimisation_target)

            if get_verbose() >= 2:
                print cost_str(current)

            if best is None:
                best = current
            else:
                if best[optimisation_target] > current[optimisation_target]:
                    best = current
                else:
                    return best
        return best
    else:
        # TODO: do not hardcode m
        log_delta_0 = log(f(RR(2)**log_eps)/alpha, 2)**2 / (4*n*log(q, 2))
        delta_0 = RR(2**log_delta_0)
        m = lattice_redution_opt_m(n, q, delta_0)
        ret = bkz_runtime_delta(delta_0, m, -log_eps)
        ret[u"ε"] = ZZ(2)**log_eps
        ret[u"oracle"] = m * success_probability/RR(2)**log_eps
        if optimisation_target != u"oracle":
            ret = cost_reorder(ret, [optimisation_target, u"oracle"])
        else:
            ret = cost_reorder(ret, [optimisation_target])
        return ret


###################################
# Section 5.4: LP Decoding attack #
###################################


@cached_function
def gsa_basis(n, q, delta, m):
    """
    Creates the basis lengths for the scaled dual

    ..  note:: based on the GSA in [RSA:LinPei11]_

    .. [RSA:LinPei11] Richard Lindner and Chris Peikert. Better key sizes (and attacks) for LWE-based encryption.
                      In Aggelos Kiayias, editor, CT-RSA 2011, volume 6558 of LNCS, pages 319–339. Springer,
                      February 2011.
    """
    RR = delta.parent()
    qnm = RR(q**(n/m))
    b = [(qnm * delta**(m - 2*m/(m-1) * i)) for i in xrange(m)]
    b = [RR(q/b[-1-i]) for i in xrange(m)]
    return b


def enum_cost(n, alpha, q, eps, delta_0, m=None, B=None, step=1, enums_per_clock=-15.1):
    """
    Estimates the runtime for performing enumeration.

    :param n:                    dimension > 0
    :param alpha:                size of the noise α < 1.0
    :param q:                    modulus > 0
    :param eps:
    :param delta_0:
    :param m:
    :param B:
    :param step:                 changes the increments for the values of d[i]
    :param enums_per_clock:      the log of the number of enumerations computed per clock cycle
    :returns:
    """

    RR = alpha.parent()
    step = RR(step)

    if B is None:
        if m is None:
            m = lattice_redution_opt_m(n, q, delta_0)
        B = gsa_basis(n, q, delta_0, m)

    d = [RR(1)]*m
    bd = [d[i] * B[i] for i in xrange(m)]
    scaling_factor = RR(sqrt(pi) / (2*alpha*q))
    probs_bd = [RR((bd[i]  * scaling_factor)).erf() for i in xrange(m)]
    success_probability = prod(probs_bd)

    bd = map(list, zip(bd, range(len(bd))))
    bd = sorted(bd)

    import bisect
    while success_probability < eps:
        v, i = bd.pop(0)
        d[i] += step
        v += B[i]*step
        success_probability /= probs_bd[i]
        probs_bd[i] = RR((v * scaling_factor).erf())
        success_probability *= probs_bd[i]
        bisect.insort_left(bd, [v, i])

    r = OrderedDict([(u"δ_0", delta_0),
                     ("enum", RR(log(prod(d), 2))),
                     ("enumop", RR(log(prod(d), 2)) - RR(enums_per_clock))])
    return r


def bdd(n, alpha, q, log_eps=None, success_probability=0.99,
        enums_per_clock=-15.1, optimisation_target="bkz2"):
    """
    Estimates the optimal parameters for decoding attack

    :param n:                    dimension > 0
    :param alpha:                size of the noise α < 1.0
    :param q:                    modulus > 0
    :param success_probability:  probability of success < 1.0
    :param enums_per_clock:      the log of the number of enumerations computed per clock cycle
    :param optimisation_target:  lattice reduction estimate to use
    """

    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)

    if log_eps is None:
        best = None
        step_size = 32
        log_eps = 1
        while True:
            current = bdd(n, alpha, q, -log_eps, success_probability,
                          enums_per_clock, optimisation_target)

            key = list(current)[0]
            if best is None:
                best = current
                log_eps += step_size
            else:
                if best[key] > current[key]:
                    best = current
                    log_eps += step_size
                else:
                    step_size = -1*step_size/2
                    log_eps += step_size

            if step_size == 0:
                break
        return best

    RR = alpha.parent()

    delta_0m1 = sis(n, alpha, q, log_eps, success_probability)[u"δ_0"] - 1
    step = RR(1.05)
    direction = -1

    repeat = ZZ(ceil(success_probability/RR(2)**log_eps))

    def combine(enum, bkz):
        enum["enum"]    = repeat *ZZ(2)**enum["enum"]
        enum["enumop"] = repeat * ZZ(2)**enum["enumop"]

        current = OrderedDict()
        current["bop"]  = enum["enumop"] + bkz[optimisation_target]

        for key in bkz:
            current[key] = bkz[key]
        for key in enum:
            current[key] = enum[key]
        current[u"ε"] = ZZ(2)**log_eps
        current[u"oracle"]  = repeat * m
        current = cost_reorder(current, ["bop", "oracle"])
        return current

    depth = 6
    while True:
        delta_0 = 1 + delta_0m1
        m = lattice_redution_opt_m(n, q, delta_0)
        bkz = bkz_runtime_delta(delta_0, m, log(repeat, 2.0))

        enum = enum_cost(n, alpha, q, RR(2)**log_eps, delta_0, m,
                         enums_per_clock=enums_per_clock)
        current = combine(enum, bkz)

        if get_verbose() >= 2:
            print cost_str(current)

        # if lattice reduction is cheaper than enumration, make it more expensive
        if current[optimisation_target] < current["enumop"]:
            prev_direction = direction
            direction = -1
            if direction != prev_direction:
                step = 1 + RR(step-1)/2
            delta_0m1 /= step
        elif current[optimisation_target] > current["enumop"]:
            prev_direction = direction
            direction = 1
            delta_0m1 *= step
        else:
            break
        if direction != prev_direction:
            step = 1 + RR(step-1)/2
            depth -= 1
        if depth == 0:
            break

    return current

###################################################
# Section 5.5: Reducing BDD to uSVP via embedding #
###################################################


def kannan(n, alpha, q, tau=tau_default, tau_prob=tau_prob_default, success_probability=0.99):
    """
    """
    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)
    RR = alpha.parent()
    beta = 1.01
    log_delta_0 = log(tau*beta*alpha*sqrt(2*e), 2)**2/(4*n*log(q, 2))
    delta_0 = RR(2**log_delta_0)

    repeat = ZZ(ceil(success_probability/tau_prob))

    m = lattice_redution_opt_m(n, q, delta_0)
    # prob = RR(1-(beta*exp(1-beta**2)/ZZ(2))**m)  # TODO: make use of it
    r = bkz_runtime_delta(delta_0, m, log(success_probability/tau_prob, 2))
    r[u"oracle"] = repeat*m  # TODO: this shouldn't be hardcoded
    r = cost_reorder(r, ["bkz2", "oracle"])
    if get_verbose() >= 2:
        print cost_str(r)
    return r


#########################
# Section 5.6: Arora-GB #
#########################


def gb_complexity(m, n, d, omega=2, call_magma=True, d2=None):
    if m > n**d:
        m = n**d

    if call_magma:
        R = magma.PowerSeriesRing(QQ, 2*n)
        z = R.gen(1)
        coeff = lambda f, d: f.Coefficient(d)
    else:
        R = PowerSeriesRing(QQ, "z", 2*n)
        z = R.gen()
        coeff = lambda f, d: f[d]

    if d2 is None:
        s = (1-z**d)**m / (1-z)**n
    else:
        s = (1-z**d)**m * (1-z**d2)**n / (1-z)**n

    retval = OrderedDict([("D", None), ("rop", None)])

    for dreg in xrange(2*n):
        if coeff(s, dreg) < 0:
            break
    else:
        return retval
    retval["D"] = dreg
    retval["rop"] = RR(binomial(n + dreg, dreg)**omega)
    retval["mem"] = RR(binomial(n + dreg, dreg)**2)
    return retval


def arora_gb(n, alpha, q, success_probability=0.99, omega=2, call_magma=True, guess=0, d2=None):

    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability,
                                                         prec=2*log(n, 2)*n)

    RR = alpha.parent()
    stddev = RR(stddevf(RR(alpha)*q))

    if stddev >= 1.1*sqrt(n):
        return None

    if d2 is True:
        d2 = 2*ceil(3*stddev)+1

    ps_single = lambda C: RR(1 - (2/(C*RR(sqrt(2*pi))) * exp(-C**2/2)))

    m = floor(exp(RR(0.75)*n))
    d = n
    t = ZZ(floor((d-1)/2))
    C = t/stddev
    pred = gb_complexity(m, n-guess, d, omega, call_magma, d2=d2)
    pred["t"] = t
    pred["oracle"] = m
    pred[u"Pr[⊥]"] = RR(m*(1-ps_single(C)))
    pred["bop"] = log(q, 2) + pred["rop"]
    pred = cost_reorder(pred, ["t", "bop", "oracle", "D"])

    if get_verbose() >= 2:
        print "PREDICTION:"
        print cost_str(pred)
        print
        print "ESTIMATION:"

    best = None
    for t in srange(t, n):
        d = 2*t + 1
        C = RR(t/stddev)
        if C < 1:  # if C is too small, we ignore it
            continue
        # Pr[success]^m = Pr[overall success]
        m = log(success_probability, 2) / log(ps_single(C), 2)
        if m < n:
            continue
        m = floor(m)

        current = gb_complexity(m, n-guess, d, omega, call_magma, d2=d2)

        if current["D"] is None:
            continue

        current["t"] = t
        current[u"Pr[⊥]"] = RR(1-success_probability)
        current["rop"] *= RR((3*stddev)**guess)
        current["bop"] = log(q, 2) * current["rop"]
        current["oracle"] = m

        current = cost_reorder(current, ["bop", "oracle", "t", "D"])

        if get_verbose() >= 2:
            print cost_str(current)

        if best is None:
            best = current
        else:
            if best["rop"] > current["rop"]:
                best = current
            else:
                break
    return best


######################################
# 6.2 Lattice Reduction Small Secret #
######################################

def small_secret_guess(f, n, alpha, q, secret_bounds, **kwds):
    size = secret_bounds[1]-secret_bounds[0] + 1
    best = None
    step_size = 16
    while step_size >= n:
        step_size /= 2
    i = 0
    while True:
        try:
            # some implementations make use of the secret_bounds parameter
            current = f(n-i, alpha, q, secret_bounds=secret_bounds, **kwds)
        except TypeError:
            current = f(n-i, alpha, q, **kwds)
        current = cost_repeat(current, size**i)

        key = list(current)[0]
        if best is None:
            best = current
            i += step_size
        else:
            if best[key] > current[key]:
                best = current
                i += step_size
            else:
                step_size = -1*step_size/2
                i += step_size

        if step_size == 0:
            break
    return best


def sis_small_secret(n, alpha, q, secret_bounds, **kwds):
    n, alpha, q = switch_modulus(n, alpha, q, uniform_variance_from_bounds(*secret_bounds))
    return small_secret_guess(sis, n, alpha, q, secret_bounds, **kwds)


def bdd_small_secret(n, alpha, q, secret_bounds, **kwds):
    n, alpha, q = switch_modulus(n, alpha, q, uniform_variance_from_bounds(*secret_bounds))
    return small_secret_guess(bdd, n, alpha, q, secret_bounds, **kwds)


def kannan_small_secret(n, alpha, q, secret_bounds, **kwds):
    n, alpha, q = switch_modulus(n, alpha, q, uniform_variance_from_bounds(*secret_bounds))
    return small_secret_guess(kannan, n, alpha, q, secret_bounds, **kwds)


def _bai_gal_small_secret(n, alpha, q, secret_bounds, tau=tau_default, tau_prob=tau_prob_default,
                          success_probability=0.99):
    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability)
    RR = alpha.parent()

    stddev = stddevf(alpha*q)

    if secret_bounds[0] == 0:
        c = 2
    else:
        c = 1

    num = 4*log(alpha)**2*log(q) \
          - 4*log(alpha)**2*log(stddev) \
          + 8*log(alpha)*log(q)*log(tau) \
          - 8*log(alpha)*log(stddev)*log(tau) \
          + 4*log(q)*log(tau)**2 \
          - 4*log(stddev)*log(tau)**2 \
          + 4*log(alpha)*log(q) \
          - 4*log(alpha)*log(stddev) \
          + 4*log(q)*log(tau) \
          - 4*log(stddev)*log(tau) \
          + log(q) \
          - log(stddev)
    den = 4*n*log(c)**2 \
          - 16*n*log(c)*log(q) \
          + 16*n*log(q)**2 \
          + 16*n*log(c)*log(stddev) \
          - 32*n*log(q)*log(stddev) \
          + 16*n*log(stddev)**2

    log_delta_0 = RR(num/den)
    delta_0 = RR(e**log_delta_0)

    repeat = ZZ(ceil(success_probability/tau_prob))

    m = ceil(sqrt(n*(log(q, 2)-log(stddev, 2))/log_delta_0))
    # prob = RR(1-(beta*exp(1-beta**2)/ZZ(2))**m)  # TODO: make use of it
    r = bkz_runtime_delta(delta_0, m, log(repeat, 2))
    r[u"oracle"] = repeat*m
    r = cost_reorder(r, ["bkz2", "oracle"])
    if get_verbose() >= 2:
        print cost_str(r)
    return r


def bai_gal_small_secret(n, alpha, q, secret_bounds, tau=tau_default, tau_prob=tau_prob_default,
                         success_probability=0.99):
    return small_secret_guess(_bai_gal_small_secret, n, alpha, q, secret_bounds,
                              tau=0.2, tau_prob=0.1, success_probability=0.99)

########################
# 6.3 BKW Small Secret #
########################


def bkw_small_secret_variances(q, a, b, kappa, o, RR=None):
    if RR is None:
        RR = RealField()
    q = RR(q)
    a = RR(a).round()
    b = RR(b)
    n = a*b
    kappa = RR(kappa)
    T = RR(2)**(b*kappa)
    n = RR(o)/RR(T*(a+1)) + RR(1)

    U_Var = lambda x: (x**2 - 1)/12
    red_var   = 2*U_Var(q/(2**kappa))

    if o:
        c_ = map(RR, [0.0000000000000000,
                      0.4057993538687922, 0.6924478992819291, 0.7898852691349439,
                      0.8441959360364506, 0.8549679124679972, 0.8954469872316165,
                      0.9157093365103325, 0.9567635780119543, 0.9434245442818547,
                      0.9987153221343770])

        M = Matrix(RR, a, a)  # rows are tables, columns are entries those tables
        for l in range(M.ncols()):
            for c in range(l, M.ncols()):
                M[l, c] = U_Var(q)

        for l in range(1, a):
            for i in range(l):
                M[l, i] = red_var + sum(M[i+1:l].column(i))

                bl = b*l
                if round(bl) < len(c_):
                    c_tau = c_[round(bl)]
                else:
                    c_tau = RR(1)/RR(5)*RR(sqrt(bl)) + RR(1)/RR(3)

                f = (c_tau*n**(~bl) + 1 - c_tau)**2
                for i in range(l):
                    M[l, i] = M[l, i]/f

        v = vector(RR, a)
        for i in range(a):
            v[i] = red_var + sum(M[i+1:].column(i))
    else:
        v = vector(RR, a)
        for i in range(a)[::-1]:
            v[i] = 2**(a-i-1) * red_var

    if get_verbose() >= 3:
        print log(red_var, 2).str(), [RealField(14)(log(x, 2)).str() for x in v]

    return v


def bkw_small_secret(n, alpha, q, success_probability=0.99, secret_bounds=(0, 1), t=None, o=0):
    """
    :param n:               number of variables in the LWE instance
    :param alpha:           standard deviation of the LWE instance
    :param q:               size of the finite field (default: n^2)
    :param secret_bounds:   minimum and maximum value of secret
    """

    def sigma2f(kappa):
        v = bkw_small_secret_variances(q, a, b, kappa, o, RR=RR)
        return sigmaf(sum([b * e * secret_variance for e in v], RR(0)).sqrt())

    def Tf(kappa):
        return min(q**b, ZZ(2)**(b*kappa))/2

    def ops_tf(kappa):
        T = Tf(kappa)
        return T * (a*(a-1)/2 * (n+1) - b*a*(a-1)/4 - b/6 * ((a-1)**3 + 3/2*(a-1)**2 + 1/RR(2)*(a-1)))

    def bkwssf(kappa):
        ret = OrderedDict()
        ret[u"κ"] = kappa
        m = bkw_required_m(sigma_final, q, success_probability, sigma2f(kappa))
        ret["m"] = m
        ret["ropsm"] = (m + o)  * (a/2 * (n + 2))
        ret["ropst"] = ops_tf(kappa)
        ret["rop"] = ret["ropst"] + ret["ropsm"]
        ret["bop"] = log(q, 2) * ret["rop"]
        T = Tf(kappa)
        ret["mem"] = T * a * (n + 1 - b * (a-1)/2)
        ret["oracle"] = T * a + ret["m"] + o
        return ret

    n, alpha, q, success_probability = preprocess_params(n, alpha, q, success_probability, prec=4*n)
    RR = alpha.parent()
    sigma = alpha*q

    if o is None:
        best = bkw_small_secret(n, alpha, q, success_probability, secret_bounds, t=t, o=0)
        o = best["oracle"]/2
        while True:
            current = bkw_small_secret(n, alpha, q, success_probability, secret_bounds, t=t, o=o)
            if best is None or current["bop"] < best["bop"]:
                best = current
            if current["bop"] > best["bop"]:
                break
            if get_verbose() >= 2:
                print cost_str(current)

            o = o/2
        return best

    if t is None:
        t = RR(2*(log(q, 2) - log(sigma, 2))/log(n, 2))
        best = None
        while True:
            current = bkw_small_secret(n, alpha, q, success_probability, secret_bounds, t=t, o=o)
            if best is None or current["bop"] < best["bop"]:
                best = current
            if current["bop"] > best["bop"]:
                break
            if get_verbose() >= 2:
                print cost_str(current)
            t += 0.01
        return best

    secret_variance = uniform_variance_from_bounds(*secret_bounds)
    secret_variance = RR(secret_variance)

    a = RR(t*log(n, 2))  # the target number of additions: a = t*log_2(n)
    b = n/a  # window width b = n/a
    sigma_final = RR(n**t).sqrt() * sigma  # after n^t additions we get this stddev
    transformation_noise = sqrt(n * 1/RR(12) * secret_variance)
    kappa = ceil(log(round(q*transformation_noise/stddevf(sigma)), 2.0)) + 1

    if kappa > ceil(log(q, 2)):
        kappa = ceil(log(q, 2))

    best = None
    while kappa > 0:
        current = bkwssf(kappa)
        if best is None or current["bop"] < best["bop"]:
            best = current
        if current["bop"] > best["bop"]:
            break
        kappa -= 1

    best["o"] = o
    best["t"] = t
    best = cost_reorder(best, ["bop", "oracle", "t", "m", "mem"])
    return best


#############################
# 6.4 Arora-GB Small Secret #
#############################

def arora_gb_small_secret(n, alpha, q, secret_bounds, **kwds):
    a, b = secret_bounds
    n, alpha, q = switch_modulus(n, alpha, q, uniform_variance_from_bounds(*secret_bounds))
    return arora_gb(n, alpha, q, d2=b-a+1, **kwds)

###########
# Overall #
###########


def estimate_lwe(n, alpha, q, skip=None, small=False, secret_bounds=None):
    if not small:
        algorithms = OrderedDict([("mitm", mitm),
                                  ("bkw", bkw),
                                  ("sis", sis),
                                  ("bdd", bdd),
                                  ("kannan", kannan),
                                  ("arora-gb", arora_gb)])
    else:
        algorithms = OrderedDict([("mitm", mitm),
                                  ("bkw", bkw_small_secret),
                                  ("sis", sis_small_secret),
                                  ("bdd", bdd_small_secret),
                                  ("kannan", kannan_small_secret),
                                  ("baigal", bai_gal_small_secret),
                                  ("arora-gb", arora_gb_small_secret)])

    if skip is None:
        skip = []
    try:
        skip = [s.strip().lower() for s in skip.split(",")]
    except AttributeError:
        pass
    skip = [s.strip().lower() for s in skip]

    alg_width = max(len(key) for key in set(algorithms).difference(skip))
    cost_kwds = {"keyword_width": 5}

    results = OrderedDict()
    for alg in algorithms:
        if alg not in skip:
            if small:
                tmp = algorithms[alg](n, alpha, q, secret_bounds=secret_bounds)
            else:
                tmp = algorithms[alg](n, alpha, q)
            if tmp:
                results[alg] = tmp
                if get_verbose() >= 1:
                    print ("%%%ds" % alg_width) % alg,
                    print cost_str(results[alg], **cost_kwds)

    return results


def plot_costs(LWE, N, skip=None, filename=None, small=False, secret_bounds=None):
    plots = {}
    for n in N:
        lwe = LWE(n)
        r = estimate_lwe(*unpack_lwe(lwe), skip=skip, small=small, secret_bounds=secret_bounds)
        for key in r:
            value = r[key].values()[0]
            plots[key] = plots.get(key, tuple()) + ((n, log(value, 2)),)

    colors = ("#4C72B0", "#55A868", "#C44E52", "#8172B2", "#CCB974", "#64B5CD")

    import matplotlib.pyplot as plt
    plt.clf()
    plt.figure(1)

    for i, plot in enumerate(plots):
        x, y = [x_ for x_, y_ in plots[plot]], [y_ for x_, y_ in plots[plot]]
        plt.plot(x, y, label=plot, color=colors[i], linewidth=1.5)

    plt.legend(loc=2)
    plt.xlabel("n")
    plt.ylabel("$\log_2$(#bops)")
    if small:
        plt.title(u"%s (%d-%d), $s ← %s^n$"%(LWE.__name__, N[0], N[-1], secret_bounds))
    else:
        plt.title(u"%s (%d-%d)"%(LWE.__name__, N[0], N[-1]))
    if filename is None:
        if small:
            small_str = "-(%d,%d)"%(secret_bounds[0], secret_bounds[1])
        else:
            small_str = ""
        filename="%s%s-%d-%d.pdf"%(LWE.__name__, small_str, N[0], N[-1])
    plt.savefig(filename, dpi=128)

################
# LaTeX tables #
################

dfs = "%4.0f"

latex_config = {
    "mitm":     OrderedDict([("bop", dfs), ("mem", dfs), ("oracle", dfs)]),
    "bkw":      OrderedDict([("bop", dfs), ("mem", dfs), ("oracle", dfs)]),
    "arora-gb": OrderedDict([("bop", dfs), ("mem", dfs), ("oracle", dfs)]),
    "sis":      OrderedDict([("bkz2", dfs), ("sieve", dfs), ("oracle", dfs), ("repeat", dfs)]),
    "kannan":   OrderedDict([("bkz2", dfs), ("sieve", dfs), ("oracle", dfs), ("repeat", dfs)]),
    "baigal":   OrderedDict([("bkz2", dfs), ("sieve", dfs), ("oracle", dfs), ("repeat", dfs)]),
    "bdd":      OrderedDict([("bop", dfs), ("enum", dfs), ("oracle", dfs), ("repeat", dfs)]),
}


def latex_cost_header(cur):
    header = []
    header.append(r"\begin{scriptsize}")

    pretty_algorithm_names = {
        "mitm": "MitM",
        "bkw":  "BKW",
        "arora-gb": "Arora-GB",
        "sis":  "SIS",
        "kannan": "Kannan",
        "baigal": "BaiGal",
        "bdd": "BDD"
    }

    pretty_column_names = {
        "oracle": "$\\Ldis$",
        "repeat": "g",
    }

    line = [r"\begin{tabular}{r"]
    for alg in cur:
        line.append("@{\hskip 8pt}")
        line.append("r" * len([key for key in latex_config[alg].keys() if key in cur[alg]]))
    line.append("}")

    header.append("".join(line))
    header.append(r"\toprule")

    line = ["    "]
    for alg in cur:
        count = len([key for key in latex_config[alg].keys() if key in cur[alg]])
        line.append(r"\multicolumn{%d}{c}{%s}"%(count, pretty_algorithm_names[alg]))
    line = " & ".join(line) + "\\\\"
    header.append(line)
    header.append(r"\midrule")

    line = [" $n$"]

    for alg in cur:
        line.extend([pretty_column_names.get(key, key) for key in latex_config[alg].keys() if key in cur[alg]])

    line = " & ".join(line) + "\\\\"
    header.append(line)
    header.append(r"\midrule")
    return header


def latex_cost_row(cur):
    line = []
    for alg in cur:
        cost = cur[alg]
        for col, format in latex_config[alg].iteritems():
            if (col == "repeat" and col in cost) or col != "repeat":
                line.append(format % log(cost[col], 2))
    return line


def latex_cost_footer(name):
    footer = []
    footer.append(r"\bottomrule")
    footer.append(r"\end{tabular}")
    footer.append(r"\end{scriptsize}")
    footer.append(r"\caption{%s}" % name)
    return footer


def latex_costs(LWE, N, skip=None, small=False, secret_bounds=None):

    ret = []
    for i, n in enumerate(N):
        line = ["%4d"%n]
        lwe = LWE(n)
        cur = estimate_lwe(*unpack_lwe(lwe), skip=skip, small=small, secret_bounds=secret_bounds)
        line.extend(latex_cost_row(cur))
        line = " & ".join(line) + "\\\\"
        ret.append(line)
        if get_verbose() >= 1:
            print

    header = latex_cost_header(cur)
    if small:
        name = "%s with $\s[(i)] \sample \{%d,%d\}$"%(LWE.__name__, secret_bounds[0], secret_bounds[1])
    else:
        name = LWE.__name__
    footer = latex_cost_footer(name)

    ret = header + ret + footer

    return "\n".join(ret)


def fhe_params(L, n):
    # Homomorphic Evaluation of the AES Circuit talks about σ^2 as variance so σ is stddev not width
    # parameter
    stddev = RR(3.2)
    xi = ZZ(8)
    q = ZZ(2)**(16.5*L + 5.4) * xi**(2*L-3) * n**L
    alpha = sigmaf(stddev)/q
    return n, alpha, q


def latex_fhe_estimates(N, l, skip=None, small=False, secret_bounds=None):

    ret = []
    for n in N:
        line = ["%6d"%n]
        params = fhe_params(l, n)
        cur = estimate_lwe(*params, skip=skip, small=small, secret_bounds=secret_bounds)
        line.extend(latex_cost_row(cur))
        line = " & ".join(line) + "\\\\"
        ret.append(line)
        if get_verbose() >= 1:
            print

    header = latex_cost_header(cur)
    footer = latex_cost_footer("FHE with L=%d"%l)

    ret = header + ret + footer
    return "\n".join(ret)
