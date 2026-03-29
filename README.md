This repository contains Magma code related to the paper *Abelian surfaces of small conductor from genus 3 double covers* by Raymond van Bommel, Celine Maistret, Jia Shi, and Andrew V. Sutherland.  It requires Magma v2.29-5 or later.  It should run on any modern x86 CPU with 8GB RAM and has been specifically tested on AMD Zen3 CPUs with 8GB RAM running Ubuntu 24.04.4 LTS.

An example use case is `magma -b P:=2 prym.m >P2.txt`, which will try to construct genus 3 double covers of elliptic curves that have good reduction away from 2.  This should take 3-5 minutes to run and produce a colon-delimited output file `P2.txt` with several hundred genus 3 double covers; most (but not all) of the corresponding Prym varieties will have good reduction away from 2.  The output file should look similar to [P2example.txt](https://github.com/AndrewVSutherland/Genus3Covers/blob/main/P2example.txt) but is not likely to be identical (or even contain the same number of lines), due to non-determinism in the algorithms used to construct the covers.

See the comments at the top of [prym.m](https://github.com/AndrewVSutherland/Genus3Covers/blob/main/prym.m) for a complete list of optional command line arguments.

The output format is *i:n:g:X:N:E:D:f:t* where

- *i* is the job id, which will be 0 by default (only relevant if you are splitting a large run over multiple jobs)
- *n* is an integer in {1,2,3} that indicates the type of the cover: 1 indicates a smooth plane quartic, 2 indicates a (rationally) hyperelliptic curve, 3 indicates a rationally hyperelliptic twist of a geometrically hyperelliptic curve
- *g* is the genus of the curve *X*, which will typically be 3, but will be 2 when a genus 2 Jacobian isogenous to the Prym can be directly computed
- *X* is a list of coefficients of a curve, whose type depends on the values of *g* and *n*.  If *g* is 2 it will be a list of two lists of coefficients of integer polynomials [coeffs(f),coeffs(h)] defining a genus 2 hyperelliptic curve y^2 + h(x)y = f(x); if *g* is 3 and *n* is 1, it will be a list of 15 coefficients of a smooth plane quartic (with monomials ordered lexicographically); otherwise it will be a list of of two lists of coefficients of integer polynomials [coeffs(f),coeffs(h)] defining a genus 3 hyperelliptic curve y^2 + h(x)y = f(x).
- *N* is the conductor of the elliptic curve *E* that is the base of the cover
- *E* is a list of five integers giving the Weierstrass coefficients of an elliptic curve
- *D* is the absolute value of the discriminant of the number field of the polynomial *f*
- *f* is an irreducible polynomial with integer coefficients defining a number field of degree at most 4 that contains the coefficients of the ramification points of the cover
- *t* is the time (in seconds) spent computing the cover

In addition to the output list of Pryms, which is written to stdout, informational/warning/error messages are written to stderr (you can control the level of detail using the `verbose` option).
