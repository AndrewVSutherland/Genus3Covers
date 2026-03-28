This repository contains Magma code related to the paper *Abelian surfaces of small conductor from genus 3 double covers* by Raymond van Bommel, Celine Maistret, Jia Shi, and Andrew V. Sutherland.

It depends on the magma package [utils](https://github.com/AndrewVSutherland/Magma/blob/main/utils.m).  If this package is not attached at startup, you should add `Attach("utils.m");` to the top of the file `prym.m`.

An example use case is `magma -b P:=2 prym.m`, which will try to construct genus 3 double covers of elliptic curves that have good reduction away from 2.  This should take 3-5 minutes to run and produce a colon-delimited output file with several hundred genus 3 double covers; most (but not all) of the corresponding Prym varieties will have good reduction away from 2.  See the top of `prym.m` for a list of command line arguments.
