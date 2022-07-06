/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang

https://github.com/leanprover-community/mathlib/blob/master/src/algebra/graded_algebra/basic.lean
-/
import group_theory.subgroup.basic

import cicm2022.internal.decomposition
import cicm2022.internal.internal
import cicm2022.external.graded_ring
import cicm2022.external.graded_algebra

/-!
# Internally-graded rings and algebras

This file defines the typeclass `graded_algebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_ring 𝒜`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  `direct_sum.decomposition 𝒜`.
* `graded_algebra 𝒜`: A convenience alias for `graded_ring` when `𝒜` is a family of submodules.
* `direct_sum.decompose_ring_equiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `direct_sum.decompose 𝒜`.
* `direct_sum.decompose_alg_equiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `direct_sum.decompose 𝒜`.
* `graded_algebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → submodule ℕ A` and `𝒜 : ι → submodule ℤ A` respectively, since all
`semiring`s are ℕ-algebras via `algebra_nat`, and all `ring`s are `ℤ`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

open_locale direct_sum big_operators

variables {ι R A σ : Type*}
section graded_ring
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ)

include A

open direct_sum

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra 𝒜`, implies an externally-graded
algebra structure `direct_sum.galgebra R (λ i, ↥(𝒜 i))`, which in turn makes available an
`algebra R (⨁ i, 𝒜 i)` instance.
-/
class graded_ring (𝒜 : ι → σ) extends set_like.graded_monoid 𝒜, direct_sum.decomposition 𝒜.

variables [graded_ring 𝒜]
namespace direct_sum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
a ring to a direct sum of components. -/
def decompose_ring_equiv : A ≃+* ⨁ i, 𝒜 i := ring_equiv.symm
{ map_mul' := (coe_ring_hom 𝒜).map_mul,
  map_add' := (coe_ring_hom 𝒜).map_add,
  ..(decompose_add_equiv 𝒜).symm }

@[simp] lemma decompose_one : decompose 𝒜 (1 : A) = 1 := map_one (decompose_ring_equiv 𝒜)
@[simp] lemma decompose_symm_one : (decompose 𝒜).symm 1 = (1 : A) :=
map_one (decompose_ring_equiv 𝒜).symm

@[simp] lemma decompose_mul (x y : A) : decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y :=
map_mul (decompose_ring_equiv 𝒜) x y
@[simp] lemma decompose_symm_mul (x y : ⨁ i, 𝒜 i) :
  (decompose 𝒜).symm (x * y) = (decompose 𝒜).symm x * (decompose 𝒜).symm y :=
map_mul (decompose_ring_equiv 𝒜).symm x y

end direct_sum

/-- The projection maps of a graded ring -/
def graded_ring.proj (i : ι) : A →+ A :=
(add_submonoid_class.subtype (𝒜 i)).comp $
  (dfinsupp.eval_add_monoid_hom i).comp $
  ring_hom.to_add_monoid_hom $ ring_equiv.to_ring_hom $ direct_sum.decompose_ring_equiv 𝒜

@[simp] lemma graded_ring.proj_apply (i : ι) (r : A) :
  graded_ring.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i := rfl

lemma graded_ring.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_ring.proj 𝒜 i ((decompose 𝒜).symm a) =
  (decompose 𝒜).symm (direct_sum.of _ i (a i)) :=
by rw [graded_ring.proj_apply, decompose_symm_of, equiv.apply_symm_apply]

lemma graded_ring.mem_support_iff [Π i (x : 𝒜 i), decidable (x ≠ 0)] (r : A) (i : ι) :
  i ∈ (decompose 𝒜 r).support ↔ graded_ring.proj 𝒜 i r ≠ 0 :=
dfinsupp.mem_support_iff.trans add_submonoid_class.coe_eq_zero.not.symm

end graded_ring

section graded_algebra
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)

/-- A special case of `graded_ring` with `σ = submodule R A`. This is useful both because it
can avoid typeclass search, and because it provides a more concise name. -/
@[reducible]
def graded_algebra := graded_ring 𝒜

/-- A helper to construct a `graded_algebra` when the `set_like.graded_monoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
@[reducible]
def graded_algebra.of_alg_hom [set_like.graded_monoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
  (right_inv : (direct_sum.coe_alg_hom 𝒜).comp decompose = alg_hom.id R A)
  (left_inv : ∀ i (x : 𝒜 i), decompose (x : A) = direct_sum.of (λ i, ↥(𝒜 i)) i x) :
  graded_algebra 𝒜 :=
{ decompose' := decompose,
  left_inv := alg_hom.congr_fun right_inv,
  right_inv := begin
    suffices : decompose.comp (direct_sum.coe_alg_hom 𝒜) = alg_hom.id _ _,
    from alg_hom.congr_fun this,
    ext i x : 2,
    exact (decompose.congr_arg $ direct_sum.coe_alg_hom_of _ _ _).trans (left_inv i x),
  end}

variable [graded_algebra 𝒜]

namespace direct_sum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
@[simps]
def decompose_alg_equiv : A ≃ₐ[R] ⨁ i, 𝒜 i := alg_equiv.symm
{ map_mul' := (coe_alg_hom 𝒜).map_mul,
  map_add' := (coe_alg_hom 𝒜).map_add,
  commutes' := (coe_alg_hom 𝒜).commutes,
  ..(decompose_add_equiv 𝒜).symm }

end direct_sum

open direct_sum

/-- The projection maps of graded algebra-/
def graded_algebra.proj (𝒜 : ι → submodule R A) [graded_algebra 𝒜] (i : ι) : A →ₗ[R] A :=
(𝒜 i).subtype.comp $
  (dfinsupp.lapply i).comp $
  (decompose_alg_equiv 𝒜).to_alg_hom.to_linear_map

@[simp] lemma graded_algebra.proj_apply (i : ι) (r : A) :
  graded_algebra.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i := rfl

lemma graded_algebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_algebra.proj 𝒜 i ((decompose 𝒜).symm a) =
  (decompose 𝒜).symm (of _ i (a i)) :=
by rw [graded_algebra.proj_apply, decompose_symm_of, equiv.apply_symm_apply]

lemma graded_algebra.mem_support_iff [decidable_eq A] (r : A) (i : ι) :
  i ∈ (decompose 𝒜 r).support ↔ graded_algebra.proj 𝒜 i r ≠ 0 :=
dfinsupp.mem_support_iff.trans submodule.coe_eq_zero.not.symm

end graded_algebra

section canonical_order

open graded_ring set_like.graded_monoid direct_sum

variables [semiring A] [decidable_eq ι]
variables [canonically_ordered_add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]

/--
If `A` is graded by a canonically ordered add monoid, then the projection map `x ↦ x₀` is a ring
homomorphism.
-/
@[simps]
def graded_ring.proj_zero_ring_hom : A →+* A :=
{ to_fun := λ a, decompose 𝒜 a 0,
  map_one' := decompose_of_mem_same 𝒜 one_mem,
  map_zero' := by simp,
  map_add' := λ _ _, by simp,
  map_mul' := λ x y, begin
    -- Convert the abstract add_submonoid into a concrete one. This is necessary as there is no
    -- lattice structure on the abstract ones.
    let 𝒜' : ι → add_submonoid A :=
      λ i, (⟨𝒜 i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid A),
    letI : graded_ring 𝒜' :=
      { decompose' := (direct_sum.decompose 𝒜 : A → ⨁ i, 𝒜 i),
        left_inv := direct_sum.decomposition.left_inv,
        right_inv := direct_sum.decomposition.right_inv,
        ..(by apply_instance : set_like.graded_monoid 𝒜), },
    have m : ∀ x, x ∈ supr 𝒜',
    { intro x,
      rw direct_sum.is_internal.add_submonoid_supr_eq_top 𝒜'
        (direct_sum.decomposition.is_internal 𝒜'),
      exact add_submonoid.mem_top x },
    refine add_submonoid.supr_induction 𝒜' (m x) (λ i c hc, _) _ _,
    { refine add_submonoid.supr_induction 𝒜' (m y) (λ j c' hc', _) _ _,
      { by_cases h : i + j = 0,
        { rw [decompose_of_mem_same 𝒜 (show c * c' ∈ 𝒜 0, from h ▸ mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c ∈ 𝒜 0, from (add_eq_zero_iff.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' ∈ 𝒜 0, from (add_eq_zero_iff.mp h).2 ▸ hc')] },
        { rw [decompose_of_mem_ne 𝒜 (mul_mem hc hc') h],
          cases (show i ≠ 0 ∨ j ≠ 0, by rwa [add_eq_zero_iff, not_and_distrib] at h) with h' h',
          { simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul] },
          { simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero] } } },
      { simp only [decompose_zero, zero_apply, add_submonoid_class.coe_zero, mul_zero], },
      { intros _ _ hd he,
        simp only [mul_add, decompose_add, add_apply, add_mem_class.coe_add, hd, he] } },
    { simp only [decompose_zero, zero_apply, add_submonoid_class.coe_zero, zero_mul] },
    { rintros _ _ ha hb,
      simp only [add_mul, decompose_add, add_apply, add_mem_class.coe_add, ha, hb] },
  end }

end canonical_order