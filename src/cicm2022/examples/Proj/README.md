# Proj construction

This folder contains an extended example (~5000 sloc) authored by Jujian Zhang ([@jjaassoonn](https://github.com/jjaassoonn)), demonstrating how to define [the $\mathrm{Proj}$ construction](https://en.wikipedia.org/wiki/Proj_construction) in algebraic geometry.
We include this for the benefit of readers looking for an extended example, but note that a full description of the formalization here is worthy of its own paper.

## Use of graded algebra API

$\mathrm{Proj}$ is a construction evolved from homogeneous prime ideals, so naturally many lemmas need to be proven for its homogeneity and primeness. In `radical.lean`, we proved a useful criterion that a homogeneous ideal ${I}$ is prime iff for all homogeneous elements $a,b\in I$, $ab\in I$ implies either $a\in I$ or $b\in I$. The way we defined graded algebra gave us a easy way to rewrite any element as sum of its projections, and the desired result can be obtained from there. Formalizing the Zariski topology involves manipulating homogeneous ideals which in turn concerns reasoning about degrees of elements. The currently formalization of graded algebra makes proving properties of homogeneous ideals a word-by-word translation of traditional maths proofs without any technical difficulty. Other objects involved in this formalization like homogeneous localizations $A\_\mathfrak p^0$ and $A^0_f$ are again easily and naturally defined through the current formalization of graded algebra. 

After $\mathrm{Proj}$ is defined, we specialize it in `n_space.lean` to the case of multivariate polynomials with the homogeneous graduation to get projective $n$-space. This is one of the most fundamental objects in the study of algebraic geometry.

As mentioned in the paper, we believe that stress testing is how we can tell if our design choice is sensible. Thus, by formalizing $\mathrm{Proj}$ and projective $n$-space, we conclude that current design choice is enough to define a set of well-functioning and natural-to-use APIs for homogeneous objects and makes reasoning about degrees of elements effortless.

## Current state in mathlib

The following files are already in mathlib and have been copied here verbatim:

* `homogeneous_ideal.lean`: homogeneous ideals and basic properties thereof
* `homogeneous_localization.lean`: homogeneous localization (the subring where numerator and denominator have the same degree)
* `topology.lean`: the Zarisky topology of $\mathrm{Proj}$
* `structure_sheaf.lean`: where $\mathcal{O}\_{\mathrm{Proj}}$

However, `Proj.lean` is not fully in mathlib yet, only the continuous map $\mathrm{Proj}A\mid\_{D(f)}\to\mathrm{Spec}A\_f^0$ is in mathlib.
