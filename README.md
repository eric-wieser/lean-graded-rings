# Graded rings in Lean’s Dependent type theory

[![DOI:10.1007/978-3-031-16681-5_8](https://img.shields.io/badge/DOI-10.1007%2F978--3--031--16681--5__8-B31B1B.svg)](https://doi.org/10.1007/978-3-031-16681-5_8)

This repository contains an executable version of the source code from the paper of the same name, submitted to CICM 2022 with abstract

> In principle, dependent type theory should provide an ideal foundation for formalizing graded rings, where each grade can be of a different type.
> However, the power of these foundations leaves a plethora of choices for how to proceed with such a formalization.
> This paper explores various different approaches to how formalization could proceed, and then demonstrates precisely how the authors formalized graded algebras in Lean's {\mathlib}.
> Notably, we show how this formalization was used as an API; allowing us to formalize graded structures such as those on tuples, free monoids, tensor algebras, and Clifford algebras.

Many of the files in this repo are virtually copies of the versions now found in mathlib; they have been separated out for convenience of presentation.
Such files are indicated by a comment of the form `From: https://github.com/leanprover-community/mathlib/blob/...` in the first few lines.
Other files are extract from in-progress pull requests. These are indicated with a similar comment.
The purpose of this extraction is to aid with understanding the scope of the paper, and to make it easier to nagivate relevant code without having to search the entirety of mathlib.

This repository contains a `.gitpod.yml` file which allows it be explored with a full vscode + lean setup in-browser, by clicking on the button below:

[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/eric-wieser/lean-graded-rings)

Note: If you arrived here by following a permalink in our paper and the top of the page does not indicate you are looking at the "master" branch, you will be looking at precisely the version that was submitted for publication. See the master branch for any corrections or information on how to cite this work.

[Slides](https://eric-wieser.github.io/cicm-2022)

## Contributors

Eric Wieser ([@eric-wieser](https://github.com/eric-wieser)), Jujian Zhang ([@jjaassoonn](https://github.com/jjaassoonn))

With thanks to Kevin Buzzard ([@kbuzzard](https://github.com/kbuzzard)) for some initial exploration.
