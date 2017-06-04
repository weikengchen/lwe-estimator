# Estimator for the Bit Security of LWE Instances

This [Sage](http://sagemath.org) module provides functions for estimating the concrete security of [Learning with Errors](https://en.wikipedia.org/wiki/Learning_with_errors) instances.

The main intend of this estimator is to give designers an easy way to choose parameters resisting known attacks and to enable cryptanalysts to compare their results and ideas with other techniques known in the literature.

## Usage Examples ##

    sage: load("https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py")
    sage: n, alpha, q = lwe_tuple(Regev(128))
    sage: costs = estimate_lwe(n, alpha, q)
    usvp red: ≈2^48.9, δ_0: 1.0099714, β: 86, d: 355, repeat: 44
     dec rop: ≈2^58.1, red: ≈2^56.8, δ_0: 1.0093107, β: 99, d: 363, babai: ≈2^42.2, babai_op: ≈2^57.3, Ldis: 363, repeat: 146, log(eps): -5
    dual red: ≈2^74.7, δ_0: 1.0088095, β: 111, Ldis: 376, |v|: 736.5210, d: 376, repeat: ≈2^19.0, log(eps): -8

## Try it online ##

You can [try the estimator online](http://aleph.sagemath.org/?z=eJxNjcEKwjAQBe-F_kPoqYXYjZWkKHgQFPyLkOhii6mJyWrx782hiO84MPOcN9e6GohC2gHYkezrckdqfbzBZJwFN-MKE42TIR8hmhnOp8MRfqgNn6opiwdnxoXBcPZke9ZJxZlohRDbXknVSbGMMyXlpi-LhKTfGK1PWK-zr7O1NFHnz_ov2HwBPwsyhw==&lang=sage) using the [Sage Math Cell](http://aleph.sagemath.org/) server. 

## Coverage ##

At present the following algorithms are covered by this estimator.

- meet-in-the-middle exhaustive search
- Coded-BKW [C:GuoJohSta15]
- dual-lattice attack and small/sparse secret variant [EC:Albrecht17]
- lattice-reduction + enumeration [RSA:LinPei11]
- primal attack via uSVP [ICISC:AlbFitGop13,ACISP:BaiGal14]
- Arora-Ge algorithm [ICALP:AroGe11] using Gröbner bases [EPRINT:ACFP14]

Above, we use [cryptobib](http://cryptobib.di.ens.fr)-style bibtex keys as references.

## Evolution ##

This code is evolving, new results are added and bugs are fixed. Hence, estimations from earlier versions might not match current estimations. This is annoying but unavoidable at present. We recommend to also state the commit that was used when referencing this project.

We also encourage authors to let us know if their paper uses this code. In particular, we thrive to tag commits with those cryptobib ePrint references that use it. For example, [this commit](https://bitbucket.org/malb/lwe-estimator/src/6295aa59048daa5d9598378386cb61887a1fe949/?at=EPRINT_Albrecht17) corresponds to this [ePrint entry](https://ia.cr/2017/047).

## Contributions ##

Our intend is for this estimator to be maintained by the research community. For example, we encourage algorithm designers to add their own algorithms to this estimator and we are happy to help with that process.

More generally, all contributions such as bugfixes, documentation and tests are welcome. Please go ahead and submit your pull requests. Also, don’t forget to add yourself to the list of contributors below in your pull requests.

At present, this estimator is maintained by Martin Albrecht. Contributors are:

- Martin Albrecht
- Florian Göpfert
- Cedric Lefebvre
- Rachel Player
- Markus Schmidt
- Sam Scott

Please follow [PEP8](https://www.python.org/dev/peps/pep-0008/) in your submissions. You can use [flake8](http://flake8.pycqa.org/en/latest/) to check for compliance. We use the following flake8 configuration (to allow longer line numbers and more complex functions):

```
[flake8]
max-line-length = 120
max-complexity = 16
ignore = E22,E241
```

## Bugs ##

If you run into a bug, please open an [issue on bitbucket](https://bitbucket.org/malb/lwe-estimator/issues?status=new&status=open). Also, please check there first if the issue has already been reported.

## Citing ##

If you use this estimator in your work, please cite

> Martin R. Albrecht, Rachel Player and Sam Scott.  
> *On the concrete hardness of Learning with Errors*.  
> Journal of Mathematical Cryptology.  
> Volume 9, Issue 3, Pages 169–203,  
> ISSN (Online) 1862-2984, ISSN (Print) 1862-2976  
> DOI: 10.1515/jmc-2015-0016, October 2015

A pre-print is available as

> Cryptology ePrint Archive, Report 2015/046, 2015.
> https://eprint.iacr.org/2015/046

A high-level overview of that work is given, for instance, in this [talk](https://martinralbrecht.files.wordpress.com/2015/05/20150507-lwe-survey-london.pdf).

