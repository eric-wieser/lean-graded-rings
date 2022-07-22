/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import cicm2022.examples.multivariate_polynomial.grading
import .Proj

/-!
# projective $n$-space

This is one of the most fundamental objects in the study of algebraic geometry.
-/

open algebraic_geometry

variables {σ R : Type*} [comm_ring R]

noncomputable def projective_n_space : Scheme := 
Proj.to_Scheme (λ i, mv_polynomial.homogeneous_submodule σ R i)
