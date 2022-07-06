/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang

From: https://github.com/leanprover-community/mathlib/blob/master/src/algebra/direct_sum/internal.lean
-/

import algebra.algebra.operations
import algebra.algebra.subalgebra.basic

import cicm2022.external.graded_algebra

/-!
# Internally graded rings and algebras
This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:
* `set_like.gnon_unital_non_assoc_semiring`
* `set_like.gsemiring`
* `set_like.gcomm_semiring`
With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:
* `direct_sum.coe_ring_hom` (a `ring_hom` version of `direct_sum.coe_add_monoid_hom`)
* `direct_sum.coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)
Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.is_internal` for providing an explicit decomposition function.
When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.
## tags
internally graded ring
-/

open_locale direct_sum big_operators

variables {ι : Type*} {σ S R : Type*}

instance add_comm_monoid.of_submonoid_on_semiring [semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) : ∀ i, add_comm_monoid (A i) :=
λ i, by apply_instance

instance add_comm_group.of_subgroup_on_semiring [ring R] [set_like σ R]
  [add_subgroup_class σ R] (A : ι → σ) : ∀ i, add_comm_group (A i) :=
λ i, by apply_instance

lemma set_like.has_graded_one.algebra_map_mem [has_zero ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.has_graded_one A] (s : S) : algebra_map S R s ∈ A 0 :=
begin
  rw algebra.algebra_map_eq_smul_one,
  exact ((A 0).smul_mem s set_like.has_graded_one.one_mem),
end

lemma set_like.has_graded_one.nat_cast_mem [has_zero ι] [add_monoid_with_one R]
  [set_like σ R] [add_submonoid_class σ R] (A : ι → σ) [set_like.has_graded_one A] (n : ℕ) :
  (n : R) ∈ A 0:=
begin
  induction n,
  { rw nat.cast_zero,
    exact zero_mem (A 0), },
  { rw nat.cast_succ,
    exact add_mem n_ih set_like.has_graded_one.one_mem, },
end

lemma set_like.has_graded_one.int_cast_mem [has_zero ι] [add_group_with_one R]
  [set_like σ R] [add_subgroup_class σ R] (A : ι → σ) [set_like.has_graded_one A] (z : ℤ) :
  (z : R) ∈ A 0:=
begin
  induction z,
  { rw int.cast_of_nat,
    exact set_like.has_graded_one.nat_cast_mem _ _, },
  { rw int.cast_neg_succ_of_nat,
    exact neg_mem (set_like.has_graded_one.nat_cast_mem _ _), },
end

section direct_sum
variables [decidable_eq ι]

/-! #### From `add_submonoid`s and `add_subgroup`s -/

namespace set_like

/-- Build a `gnon_unital_non_assoc_semiring` instance for a collection of additive submonoids. -/
instance gnon_unital_non_assoc_semiring [has_add ι] [non_unital_non_assoc_semiring R]
  [set_like σ R] [add_submonoid_class σ R]
  (A : ι → σ) [set_like.has_graded_mul A] :
  direct_sum.gnon_unital_non_assoc_semiring (λ i, A i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  ..set_like.ghas_mul A }

/-- Build a `gsemiring` instance for a collection of additive submonoids. -/
instance gsemiring [add_monoid ι] [semiring R] [set_like σ R] [add_submonoid_class σ R]
  (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  nat_cast := λ n, ⟨n, set_like.has_graded_one.nat_cast_mem _ _⟩,
  nat_cast_zero := subtype.ext nat.cast_zero,
  nat_cast_succ := λ n, subtype.ext (nat.cast_succ n),
  ..set_like.gmonoid A }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcomm_semiring [add_comm_monoid ι] [comm_semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gcomm_semiring (λ i, A i) :=
{ ..set_like.gcomm_monoid A,
  ..set_like.gsemiring A, }

/-- Build a `gring` instance for a collection of additive subgroups. -/
instance gring [add_monoid ι] [ring R] [set_like σ R] [add_subgroup_class σ R]
  (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gring (λ i, A i) :=
{ int_cast := λ z, ⟨z, set_like.has_graded_one.int_cast_mem _ _⟩,
  int_cast_of_nat := λ n, subtype.ext $ int.cast_of_nat _,
  int_cast_neg_succ_of_nat := λ n, subtype.ext $ int.cast_neg_succ_of_nat n,
  ..set_like.gsemiring A }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcomm_ring [add_comm_monoid ι] [comm_ring R] [set_like σ R]
  [add_subgroup_class σ R] (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gcomm_ring (λ i, A i) :=
{ ..set_like.gcomm_monoid A,
  ..set_like.gring A, }

end set_like

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def direct_sum.coe_ring_hom [add_monoid ι] [semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) [set_like.graded_monoid A] : (⨁ i, A i) →+* R :=
direct_sum.to_semiring (λ i, add_submonoid_class.subtype (A i)) rfl (λ _ _ _ _, rfl)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp] lemma direct_sum.coe_ring_hom_of [add_monoid ι] [semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) [set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.coe_ring_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ _ _ _ _

lemma direct_sum.coe_mul_apply [add_monoid ι] [semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) [set_like.graded_monoid A]
  [Π (i : ι) (x : A i), decidable (x ≠ 0)] (r r' : ⨁ i, A i) (i : ι) :
  ((r * r') i : R) =
    ∑ ij in finset.filter (λ ij : ι × ι, ij.1 + ij.2 = i) (r.support.product r'.support),
      r ij.1 * r' ij.2 :=
begin
  rw [direct_sum.mul_eq_sum_support_ghas_mul, dfinsupp.finset_sum_apply,
    add_submonoid_class.coe_finset_sum],
  simp_rw [direct_sum.coe_of_apply, ←finset.sum_filter, set_like.coe_ghas_mul],
end

/-! #### From `submodule`s -/

namespace submodule

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] :
  direct_sum.galgebra S (λ i, A i) :=
{ to_fun := ((algebra.linear_map S R).cod_restrict (A 0) $
    set_like.has_graded_one.algebra_map_mem A).to_add_monoid_hom,
  map_one := subtype.ext $ by exact (algebra_map S R).map_one,
  map_mul := λ x y, sigma.subtype_ext (add_zero 0).symm $ (algebra_map S R).map_mul _ _,
  commutes := λ r ⟨i, xi⟩,
    sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) $ algebra.commutes _ _,
  smul_def := λ r ⟨i, xi⟩, sigma.subtype_ext (zero_add i).symm $ algebra.smul_def _ _ }

@[simp] lemma set_like.coe_galgebra_to_fun [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] (s : S) :
    ↑(@direct_sum.galgebra.to_fun _ S (λ i, A i) _ _ _ _ _ _ _ s) = (algebra_map S R s : R) := rfl

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_graded_monoid
  [comm_semiring S] [semiring R] [algebra S R] (p : submodule S R) :
  set_like.graded_monoid (λ i : ℕ, p ^ i) :=
{ one_mem := by { rw [←one_le, pow_zero], exact le_rfl },
  mul_mem := λ i j p q hp hq, by { rw pow_add, exact submodule.mul_mem_mul hp hq } }

end submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def direct_sum.coe_alg_hom [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] : (⨁ i, A i) →ₐ[S] R :=
direct_sum.to_algebra S _ (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) (λ _, rfl)

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`direct_sum.coe_alg_hom`. -/
lemma submodule.supr_eq_to_submodule_range [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R] (A : ι → submodule S R) [set_like.graded_monoid A] :
  (⨆ i, A i) = (direct_sum.coe_alg_hom A).range.to_submodule :=
(submodule.supr_eq_range_dfinsupp_lsum A).trans $ set_like.coe_injective rfl

@[simp] lemma direct_sum.coe_alg_hom_of [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.coe_alg_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ rfl (λ _ _ _ _, rfl) _ _

end direct_sum

section homogeneous_element

lemma set_like.is_homogeneous_zero_submodule [has_zero ι]
  [semiring S] [add_comm_monoid R] [module S R]
  (A : ι → submodule S R) : set_like.is_homogeneous A (0 : R) :=
⟨0, submodule.zero_mem _⟩

lemma set_like.is_homogeneous.smul [comm_semiring S] [semiring R] [algebra S R]
  {A : ι → submodule S R} {s : S}
  {r : R} (hr : set_like.is_homogeneous A r) : set_like.is_homogeneous A (s • r) :=
let ⟨i, hi⟩ := hr in ⟨i, submodule.smul_mem _ _ hi⟩

end homogeneous_element