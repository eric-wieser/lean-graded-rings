# Graded rings in Lean’s Dependent type theory

This repository contains an executable version of the source code from the paper of the same name, submitted to CICM 2022 with abstract

> In principle, dependent type theory should provide an ideal foundation for formalizing graded rings, where each grade can be of a different type.
> With such a powerful foundation comes a large number of choices for how to proceed with such a formalization.
> This paper explores various different approaches to how formalization could proceed, and then demonstrates precisely how graded algebras were formalized in Lean's mathlib.
> Notably, we show how this formalization was used as an API; allowing us to formalize various types of graded structure such as those on tuples, free monoids, tensor algebras, and Clifford algebras.

Many of the files in this repo are virtually copies of the versions now found in mathlib; they have been separated out for convenience of presentation.
Such files are indicated by a comment of the form `https://github.com/leanprover-community/mathlib/blob/...` in the first few lines.

This repository contains a `.gitpod.yml` file which allows it be explored with a full vscode + lean setup in-browser, by clicking on the button below:

[![Gitpod ready-to-code](https://img.shields.io/badge/Gitpod-ready--to--code-908a85?logo=gitpod)](https://gitpod.io/#https://github.com/eric-wieser/lean-graded-rings)

## Contributors

Eric Wieser (@eric-wieser), Jujian Zhang (@jjaassoonn)
