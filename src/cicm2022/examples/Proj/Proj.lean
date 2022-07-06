/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.Spec
import algebraic_geometry.Scheme

import .Proj_iso_Spec.Sheaf_component.iso

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`       : the degree zero part of localized ring `Aₓ`

## Implementation

In `src/algebraic_geometry/projective_spectrum/structure_sheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous element of positive degree.
2. We prove that for any `f : A`, `Proj.T | (pbo f)` is homeomorphic to `Spec.T A⁰_f`:
  - forward direction :
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `x ∩ span {g / 1 | g ∈ A}` (see `Top_component.forward.carrier`). This ideal is prime, the proof
    is in `Top_component.forward.to_fun`. The fact that this function is continuous is found in
    `Top_component.forward`
  - backward direction : TBC

## Main Definitions and Statements

* `degree_zero_part`: the degree zero part of the localized ring `Aₓ` where `x` is a homogeneous
  element of degree `n` is the subring of elements of the form `a/f^m` where `a` has degree `mn`.

For a homogeneous element `f` of degree `n`
* `Top_component.forward`: `forward f` is the
  continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
* `Top_component.forward.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero, then the preimage
  of `sbo a/f^m` under `forward f` is `pbo f ∩ pbo a`.


* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like.graded_monoid localization finset (hiding mk_zero)

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜]

open Top topological_space
open category_theory opposite
open projective_spectrum.structure_sheaf

local notation `Proj` := Proj.to_LocallyRingedSpace 𝒜
-- `Proj` as a locally ringed space
local notation `Proj.T` := Proj .1.1.1
-- the underlying topological space of `Proj`
local notation `Proj| ` U := Proj .restrict (opens.open_embedding (U : opens Proj.T))
-- `Proj` restrict to some open set
local notation `Proj.T| ` U :=
  (Proj .restrict (opens.open_embedding (U : opens Proj.T))).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Proj` restricted to some open set
local notation `pbo` x := projective_spectrum.basic_open 𝒜 x
-- basic open sets in `Proj`
local notation `sbo` f := prime_spectrum.basic_open f
-- basic open sets in `Spec`
local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)
-- `Spec` as a locally ringed space
local notation `Spec.T` ring :=
  (Spec.LocallyRingedSpace_obj (CommRing.of ring)).to_SheafedSpace.to_PresheafedSpace.1
-- the underlying topological space of `Spec`
local notation `A⁰_` f_deg := degree_zero_part f_deg

def choose_element (x : Proj) :
  Σ' (n : ℕ) (hn : 0 < n) (f : A), f ∈ 𝒜 n ∧ f ∉ x.as_homogeneous_ideal :=
begin
  classical,
  have := x.2.2,
  erw set.not_subset at this,
  choose f h1 h2 using this,
  erw ←direct_sum.sum_support_decompose 𝒜 f at h2,
  have : ∃ (n : ℕ) (hn : 0 < n), (direct_sum.decompose 𝒜 f n : A) ∉ x.as_homogeneous_ideal.1,
  { by_contra rid,
    simp only [not_exists, exists_prop, not_and, not_not, subtype.val_eq_coe] at rid,
    apply h2,
    apply ideal.sum_mem,
    intros c hc,
    by_cases ineq1 : 0 < c,
    { apply rid _ ineq1, },
    { rw not_lt at ineq1,
      replace ineq1 := nat.eq_zero_of_le_zero ineq1,
      rw ineq1,
      dsimp only at h1,
      change f ∈ (homogeneous_ideal.irrelevant 𝒜) at h1,
      rw ←graded_algebra.proj_apply,
      rw homogeneous_ideal.mem_irrelevant_iff at h1,
      erw h1,
      exact submodule.zero_mem _, },
    },
  choose n hn1 hn2 using this,
  refine ⟨n, hn1, (direct_sum.decompose _ f n : A), submodule.coe_mem _, hn2⟩,
end

def Proj.to_Scheme : Scheme :=
{ local_affine := λ x, 
  begin
    rcases choose_element 𝒜 x with ⟨n, hn, f, f_deg, mem⟩,
    refine ⟨⟨pbo f, mem⟩, ⟨A⁰_ f_deg⟩, ⟨Proj_iso_Spec_Sheaf_component.iso 𝒜 f_deg hn⟩⟩,
  end,
  ..Proj }

end algebraic_geometry
