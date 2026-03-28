This repository contains Magma code related to the paper *Abelian surfaces of small conductor from genus 3 double covers* by Raymond van Bommel, Celine Maistret, Jia Shi, and Andrew V. Sutherland.

It depends on the magma package [utils](https://github.com/AndrewVSutherland/Magma/blob/main/utils.m).  If this package is not attached at startup, you should add `Attach("utils.m");` to the top of the file `prym.m`.

An example use case is `magma -b P:=2 prym.m`, which will try to construct genus 3 double covers of elliptic curves that have good reduction away from 2.  This should take 3-5 minutes to run and produce a colon-delimited output file with several hundred genus 3 double covers; most (but not all) of the corresponding Prym varieties will have good reduction away from 2.  See the comments at the top of [prym.m](https://github.com/AndrewVSutherland/Genus3Covers/blob/main/prym.m) for a complete list of optional command line arguments.

In addition to the output list of Pryms, which is written to stdout, informational/warning/error messages are written to stderr (you can control the level of detail using the `verbose` option).
