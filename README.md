# Estimator for the Bit Security of LWE Instances

This [Sage](http://sagemath.org) module provides functions for estimating the bit security of [Learning with Errors](https://en.wikipedia.org/wiki/Learning_with_errors) instances.

## Usage Examples ##

    sage: load("https://bitbucket.org/malb/lwe-estimator/raw/HEAD/estimator.py")
    sage: n, alpha, q = unpack_lwe(Regev(128))
    sage: set_verbose(1)
    sage: costs = estimate_lwe(n, alpha, q, skip="arora-gb")
    sage: print cost_str(costs["dec"])
    bop:   ≈2^56.1,  oracle:   ≈2^14.5,  δ_0: 1.0097372,  bkz2:   ≈2^55.0,  k:        90,  fplll:  ≈2^126.0,  sieve:   ≈2^63.8,  enum:   ≈2^40.2,  enumop:   ≈2^55.3,  ε: 0.0625000

## Try it online ##

You can [try the estimator online](http://aleph.sagemath.org/?z=eJxNjcEKwjAQBe-F_kPoqYXYjZWkKHgQFPyLkOhii6mJyWrx782hiO84MPOcN9e6GohC2gHYkezrckdqfbzBZJwFN-MKE42TIR8hmhnOp8MRfqgNn6opiwdnxoXBcPZke9ZJxZlohRDbXknVSbGMMyXlpi-LhKTfGK1PWK-zr7O1NFHnz_ov2HwBPwsyhw==&lang=sage) using the [Sage Math Cell](http://aleph.sagemath.org/) server. 

## Citing ##

If you use this estimator in your work, please cite

Martin R. Albrecht and Rachel Player and Sam Scott.
*On the concrete hardness of Learning with Errors*.
Cryptology ePrint Archive, Report 2015/046, 2015.
https://eprint.iacr.org/2015/046

A high-level overview of that work is given, for instance, in this [talk](https://martinralbrecht.files.wordpress.com/2015/05/20150507-lwe-survey-london.pdf).
