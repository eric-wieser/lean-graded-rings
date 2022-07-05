/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

https://github.com/leanprover-community/mathlib/blob/master/src/algebra/direct_sum/graded_ring.lean
-/
import group_theory.subgroup.basic
import algebra.direct_sum.basic
import algebra.big_operators.pi

import cicm2022.external.graded_monoid

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.gnon_unital_non_assoc_semiring A`
* `direct_sum.gsemiring A`
* `direct_sum.gring A`
* `direct_sum.gcomm_semiring A`
* `direct_sum.gcomm_ring A`

Respectively, these imbue the external direct sum `⨁ i, A i` with:

* `direct_sum.non_unital_non_assoc_semiring`, `direct_sum.non_unital_non_assoc_ring`
* `direct_sum.semiring`
* `direct_sum.ring`
* `direct_sum.comm_semiring`
* `direct_sum.comm_ring`

the base ring `A 0` with:

* `direct_sum.grade_zero.non_unital_non_assoc_semiring`,
  `direct_sum.grade_zero.non_unital_non_assoc_ring`
* `direct_sum.grade_zero.semiring`
* `direct_sum.grade_zero.ring`
* `direct_sum.grade_zero.comm_semiring`
* `direct_sum.grade_zero.comm_ring`

and the `i`th grade `A i` with `A 0`-actions (`•`) defined as left-multiplication:

* `direct_sum.grade_zero.has_smul (A 0)`, `direct_sum.grade_zero.smul_with_zero (A 0)`
* `direct_sum.grade_zero.module (A 0)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`direct_sum.of_zero_ring_hom : A 0 →+* ⨁ i, A i` provides `direct_sum.of A 0` as a ring
homomorphism.

`direct_sum.to_semiring` extends `direct_sum.to_add_monoid` to produce a `ring_hom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `gsemiring` and `gcomm_semiring`
instances for:

* `A : ι → submonoid S`:
  `direct_sum.gsemiring.of_add_submonoids`, `direct_sum.gcomm_semiring.of_add_submonoids`.
* `A : ι → subgroup S`:
  `direct_sum.gsemiring.of_add_subgroups`, `direct_sum.gcomm_semiring.of_add_subgroups`.
* `A : ι → submodule S`:
  `direct_sum.gsemiring.of_submodules`, `direct_sum.gcomm_semiring.of_submodules`.

If `complete_lattice.independent (set.range A)`, these provide a gradation of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/

set_option old_structure_cmd true

variables {ι : Type*} [decidable_eq ι]

namespace direct_sum

open_locale direct_sum

/-! ### Typeclasses -/
section defs

variables (A : ι → Type*)

/-- A graded version of `non_unital_non_assoc_semiring`. -/
class gnon_unital_non_assoc_semiring [has_add ι] [Π i, add_comm_monoid (A i)] extends
  graded_monoid.ghas_mul A :=
(mul_zero : ∀ {i j} (a : A i), mul a (0 : A j) = 0)
(zero_mul : ∀ {i j} (b : A j), mul (0 : A i) b = 0)
(mul_add : ∀ {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c)
(add_mul : ∀ {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c)

end defs

section defs

variables (A : ι → Type*)

/-- A graded version of `semiring`. -/
class gsemiring [add_monoid ι] [Π i, add_comm_monoid (A i)] extends
  gnon_unital_non_assoc_semiring A, graded_monoid.gmonoid A :=
(nat_cast : ℕ → A 0)
(nat_cast_zero : nat_cast 0 = 0)
(nat_cast_succ : ∀ n : ℕ, nat_cast (n + 1) = nat_cast n + graded_monoid.ghas_one.one)

/-- A graded version of `comm_semiring`. -/
class gcomm_semiring [add_comm_monoid ι] [Π i, add_comm_monoid (A i)] extends
  gsemiring A, graded_monoid.gcomm_monoid A

/-- A graded version of `ring`. -/
class gring [add_monoid ι] [Π i, add_comm_group (A i)] extends gsemiring A :=
(int_cast : ℤ → A 0)
(int_cast_of_nat : ∀ n : ℕ, int_cast n = nat_cast n)
(int_cast_neg_succ_of_nat : ∀ n : ℕ, int_cast (-(n+1 : ℕ)) = -nat_cast (n+1 : ℕ))

/-- A graded version of `comm_ring`. -/
class gcomm_ring [add_comm_monoid ι] [Π i, add_comm_group (A i)] extends
  gring A, gcomm_semiring A

end defs

lemma of_eq_of_graded_monoid_eq {A : ι → Type*} [Π (i : ι), add_comm_monoid (A i)]
  {i j : ι} {a : A i} {b : A j} (h : graded_monoid.mk i a = graded_monoid.mk j b) :
  direct_sum.of A i a = direct_sum.of A j b :=
dfinsupp.single_eq_of_sigma_eq h

variables (A : ι → Type*)

/-! ### Instances for `⨁ i, A i` -/


section one
variables [has_zero ι] [graded_monoid.ghas_one A] [Π i, add_comm_monoid (A i)]

instance : has_one (⨁ i, A i) :=
{ one := direct_sum.of (λ i, A i) 0 graded_monoid.ghas_one.one }

end one

section mul
variables [has_add ι] [Π i, add_comm_monoid (A i)] [gnon_unital_non_assoc_semiring A]

open add_monoid_hom (flip_apply coe_comp comp_hom_apply_apply)

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gmul_hom {i j} : A i →+ A j →+ A (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, graded_monoid.ghas_mul.mul a b,
    map_zero' := gnon_unital_non_assoc_semiring.mul_zero _,
    map_add' := gnon_unital_non_assoc_semiring.mul_add _ },
  map_zero' := add_monoid_hom.ext $ λ a, gnon_unital_non_assoc_semiring.zero_mul a,
  map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ b, gnon_unital_non_assoc_semiring.add_mul _ _ _}

/-- The multiplication from the `has_mul` instance, as a bundled homomorphism. -/
def mul_hom : (⨁ i, A i) →+ (⨁ i, A i) →+ ⨁ i, A i :=
direct_sum.to_add_monoid $ λ i,
  add_monoid_hom.flip $ direct_sum.to_add_monoid $ λ j, add_monoid_hom.flip $
    (direct_sum.of A _).comp_hom.comp $ gmul_hom A

instance : non_unital_non_assoc_semiring (⨁ i, A i) :=
{ mul := λ a b, mul_hom A a b,
  zero := 0,
  add := (+),
  zero_mul := λ a, by simp only [add_monoid_hom.map_zero, add_monoid_hom.zero_apply],
  mul_zero := λ a, by simp only [add_monoid_hom.map_zero],
  left_distrib := λ a b c, by simp only [add_monoid_hom.map_add],
  right_distrib := λ a b c, by simp only [add_monoid_hom.map_add, add_monoid_hom.add_apply],
  .. direct_sum.add_comm_monoid _ _}

variables {A}

lemma mul_hom_of_of {i j} (a : A i) (b : A j) :
  mul_hom A (of _ i a) (of _ j b) = of _ (i + j) (graded_monoid.ghas_mul.mul a b) :=
begin
  unfold mul_hom,
  rw [to_add_monoid_of, flip_apply, to_add_monoid_of, flip_apply, coe_comp, function.comp_app,
      comp_hom_apply_apply, coe_comp, function.comp_app, gmul_hom_apply_apply],
end

lemma of_mul_of {i j} (a : A i) (b : A j) :
  of _ i a * of _ j b = of _ (i + j) (graded_monoid.ghas_mul.mul a b) :=
mul_hom_of_of a b

end mul

section semiring
variables [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A]

open add_monoid_hom (flip_hom coe_comp comp_hom_apply_apply flip_apply flip_hom_apply)

private lemma one_mul (x : ⨁ i, A i) : 1 * x = x :=
suffices mul_hom A 1 = add_monoid_hom.id (⨁ i, A i),
  from add_monoid_hom.congr_fun this x,
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw mul_hom_of_of,
  exact of_eq_of_graded_monoid_eq (one_mul $ graded_monoid.mk i xi),
end

private lemma mul_one (x : ⨁ i, A i) : x * 1 = x :=
suffices (mul_hom A).flip 1 = add_monoid_hom.id (⨁ i, A i),
  from add_monoid_hom.congr_fun this x,
begin
  apply add_hom_ext, intros i xi,
  unfold has_one.one,
  rw [flip_apply, mul_hom_of_of],
  exact of_eq_of_graded_monoid_eq (mul_one $ graded_monoid.mk i xi),
end

private lemma mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) :=
suffices (mul_hom A).comp_hom.comp (mul_hom A)            -- `λ a b c, a * b * c` as a bundled hom
       = (add_monoid_hom.comp_hom flip_hom $              -- `λ a b c, a * (b * c)` as a bundled hom
             (mul_hom A).flip.comp_hom.comp (mul_hom A)).flip,
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b) c,
begin
  ext ai ax bi bx ci cx : 6,
  dsimp only [coe_comp, function.comp_app, comp_hom_apply_apply, flip_apply, flip_hom_apply],
  rw [mul_hom_of_of, mul_hom_of_of, mul_hom_of_of, mul_hom_of_of],
  exact of_eq_of_graded_monoid_eq (mul_assoc (graded_monoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩),
end

/-- The `semiring` structure derived from `gsemiring A`. -/
instance semiring : semiring (⨁ i, A i) :=
{ one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  one_mul := one_mul A,
  mul_one := mul_one A,
  mul_assoc := mul_assoc A,
  nat_cast := λ n, of _ _ (gsemiring.nat_cast n),
  nat_cast_zero := by rw [gsemiring.nat_cast_zero, map_zero],
  nat_cast_succ := λ n, by { rw [gsemiring.nat_cast_succ, map_add], refl },
  ..direct_sum.non_unital_non_assoc_semiring _, }

lemma of_pow {i} (a : A i) (n : ℕ) :
  of _ i a ^ n = of _ (n • i) (graded_monoid.gmonoid.gnpow _ a) :=
begin
  induction n with n,
  { exact of_eq_of_graded_monoid_eq (pow_zero $ graded_monoid.mk _ a).symm, },
  { rw [pow_succ, n_ih, of_mul_of],
    exact of_eq_of_graded_monoid_eq (pow_succ (graded_monoid.mk _ a) n).symm, },
end

lemma of_list_dprod {α} (l : list α) (fι : α → ι) (fA : Π a, A (fι a)) :
  of A _ (l.dprod fι fA) = (l.map $ λ a, of A (fι a) (fA a)).prod :=
begin
  induction l,
  { simp only [list.map_nil, list.prod_nil, list.dprod_nil],
    refl },
  { simp only [list.map_cons, list.prod_cons, list.dprod_cons, ←l_ih, direct_sum.of_mul_of],
    refl },
end

lemma list_prod_of_fn_of_eq_dprod (n : ℕ) (fι : fin n → ι) (fA : Π a, A (fι a)) :
  (list.of_fn $ λ a, of A (fι a) (fA a)).prod = of A _ ((list.fin_range n).dprod fι fA) :=
by rw [list.of_fn_eq_map, of_list_dprod]

open_locale big_operators

/-- A heavily unfolded version of the definition of multiplication -/
lemma mul_eq_sum_support_ghas_mul
  [Π (i : ι) (x : A i), decidable (x ≠ 0)] (a a' : ⨁ i, A i) :
  a * a' =
    ∑ (ij : ι × ι) in (dfinsupp.support a).product (dfinsupp.support a'),
      direct_sum.of _ _ (graded_monoid.ghas_mul.mul (a ij.fst) (a' ij.snd)) :=
begin
  change direct_sum.mul_hom _ a a' = _,
  dsimp [direct_sum.mul_hom, direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply],
  simp only [dfinsupp.sum_add_hom_apply, dfinsupp.sum, dfinsupp.finset_sum_apply,
    add_monoid_hom.coe_finset_sum, finset.sum_apply, add_monoid_hom.flip_apply,
    add_monoid_hom.comp_hom_apply_apply, add_monoid_hom.comp_apply,
    direct_sum.gmul_hom_apply_apply],
  rw finset.sum_product,
end

end semiring

section comm_semiring

variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_semiring A]

private lemma mul_comm (a b : ⨁ i, A i) : a * b = b * a :=
suffices mul_hom A = (mul_hom A).flip,
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b,
begin
  apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx,
  rw [add_monoid_hom.flip_apply, mul_hom_of_of, mul_hom_of_of],
  exact of_eq_of_graded_monoid_eq (gcomm_semiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩),
end

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance comm_semiring : comm_semiring (⨁ i, A i) :=
{ one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  mul_comm := mul_comm A,
  ..direct_sum.semiring _, }

end comm_semiring

section non_unital_non_assoc_ring
variables [Π i, add_comm_group (A i)] [has_add ι] [gnon_unital_non_assoc_semiring A]

/-- The `ring` derived from `gsemiring A`. -/
instance non_assoc_ring : non_unital_non_assoc_ring (⨁ i, A i) :=
{ mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.non_unital_non_assoc_semiring _),
  ..(direct_sum.add_comm_group _), }

end non_unital_non_assoc_ring

section ring
variables [Π i, add_comm_group (A i)] [add_monoid ι] [gring A]

/-- The `ring` derived from `gsemiring A`. -/
instance ring : ring (⨁ i, A i) :=
{ one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  int_cast := λ z, of _ _ (gring.int_cast z),
  int_cast_of_nat := λ z, congr_arg _ $ gring.int_cast_of_nat _,
  int_cast_neg_succ_of_nat := λ z,
    (congr_arg _ $ gring.int_cast_neg_succ_of_nat _).trans (map_neg _ _),
  ..(direct_sum.semiring _),
  ..(direct_sum.add_comm_group _), }

end ring

section comm_ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_ring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance comm_ring : comm_ring (⨁ i, A i) :=
{ one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring _),
  ..(direct_sum.comm_semiring _), }

end comm_ring


/-! ### Instances for `A 0`

The various `g*` instances are enough to promote the `add_comm_monoid (A 0)` structure to various
types of multiplicative structure.
-/

section grade_zero

section one
variables [has_zero ι] [graded_monoid.ghas_one A] [Π i, add_comm_monoid (A i)]

@[simp] lemma of_zero_one : of _ 0 (1 : A 0) = 1 := rfl

end one

section mul
variables [add_zero_class ι] [Π i, add_comm_monoid (A i)] [gnon_unital_non_assoc_semiring A]

@[simp] lemma of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
(of_eq_of_graded_monoid_eq (graded_monoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp] lemma of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b:=
of_zero_smul A a b

instance grade_zero.non_unital_non_assoc_semiring : non_unital_non_assoc_semiring (A 0) :=
function.injective.non_unital_non_assoc_semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of A 0).map_add (of_zero_mul A) (λ x n, dfinsupp.single_smul n x)

instance grade_zero.smul_with_zero (i : ι) : smul_with_zero (A 0) (A i) :=
begin
  letI := smul_with_zero.comp_hom (⨁ i, A i) (of A 0).to_zero_hom,
  refine dfinsupp.single_injective.smul_with_zero (of A i).to_zero_hom (of_zero_smul A),
end

end mul

section semiring
variables [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A]

@[simp] lemma of_zero_pow (a : A 0) : ∀ n : ℕ, of _ 0 (a ^ n) = of _ 0 a ^ n
| 0 := by rw [pow_zero, pow_zero, direct_sum.of_zero_one]
| (n + 1) := by rw [pow_succ, pow_succ, of_zero_mul, of_zero_pow]

instance : has_nat_cast (A 0) := ⟨gsemiring.nat_cast⟩

@[simp] lemma of_nat_cast (n : ℕ) : of A 0 n = n :=
rfl

/-- The `semiring` structure derived from `gsemiring A`. -/
instance grade_zero.semiring : semiring (A 0) :=
function.injective.semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (of A 0).map_nsmul (λ x n, of_zero_pow _ _ _) (of_nat_cast A)

/-- `of A 0` is a `ring_hom`, using the `direct_sum.grade_zero.semiring` structure. -/
def of_zero_ring_hom : A 0 →+* (⨁ i, A i) :=
{ map_one' := of_zero_one A, map_mul' := of_zero_mul A, ..(of _ 0) }

/-- Each grade `A i` derives a `A 0`-module structure from `gsemiring A`. Note that this results
in an overall `module (A 0) (⨁ i, A i)` structure via `direct_sum.module`.
-/
instance grade_zero.module {i} : module (A 0) (A i) :=
begin
  letI := module.comp_hom (⨁ i, A i) (of_zero_ring_hom A),
  exact dfinsupp.single_injective.module (A 0) (of A i) (λ a, of_zero_smul A a),
end

end semiring

section comm_semiring

variables [Π i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_semiring A]

/-- The `comm_semiring` structure derived from `gcomm_semiring A`. -/
instance grade_zero.comm_semiring : comm_semiring (A 0) :=
function.injective.comm_semiring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (λ x n, dfinsupp.single_smul n x) (λ x n, of_zero_pow _ _ _) (of_nat_cast A)

end comm_semiring

section ring
variables [Π i, add_comm_group (A i)] [add_zero_class ι] [gnon_unital_non_assoc_semiring A]

/-- The `non_unital_non_assoc_ring` derived from `gnon_unital_non_assoc_semiring A`. -/
instance grade_zero.non_unital_non_assoc_ring : non_unital_non_assoc_ring (A 0) :=
function.injective.non_unital_non_assoc_ring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of A 0).map_add (of_zero_mul A)
  (of A 0).map_neg (of A 0).map_sub
  (λ x n, begin
    letI : Π i, distrib_mul_action ℕ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end)
  (λ x n, begin
    letI : Π i, distrib_mul_action ℤ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end)

end ring

section ring
variables [Π i, add_comm_group (A i)] [add_monoid ι] [gring A]

instance : has_int_cast (A 0) := ⟨gring.int_cast⟩

@[simp] lemma of_int_cast (n : ℤ) : of A 0 n = n :=
rfl

/-- The `ring` derived from `gsemiring A`. -/
instance grade_zero.ring : ring (A 0) :=
function.injective.ring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (of A 0).map_neg (of A 0).map_sub
  (λ x n, begin
    letI : Π i, distrib_mul_action ℕ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end)
  (λ x n, begin
    letI : Π i, distrib_mul_action ℤ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end) (λ x n, of_zero_pow _ _ _)
  (of_nat_cast A) (of_int_cast A)

end ring

section comm_ring
variables [Π i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_ring A]

/-- The `comm_ring` derived from `gcomm_semiring A`. -/
instance grade_zero.comm_ring : comm_ring (A 0) :=
function.injective.comm_ring (of A 0) dfinsupp.single_injective
  (of A 0).map_zero (of_zero_one A) (of A 0).map_add (of_zero_mul A)
  (of A 0).map_neg (of A 0).map_sub
  (λ x n, begin
    letI : Π i, distrib_mul_action ℕ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end)
  (λ x n, begin
    letI : Π i, distrib_mul_action ℤ (A i) := λ i, infer_instance,
    exact dfinsupp.single_smul n x
  end) (λ x n, of_zero_pow _ _ _)
  (of_nat_cast A) (of_int_cast A)

end comm_ring

end grade_zero

section to_semiring

variables {R : Type*} [Π i, add_comm_monoid (A i)] [add_monoid ι] [gsemiring A] [semiring R]
variables {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
lemma ring_hom_ext' ⦃F G : (⨁ i, A i) →+* R⦄
  (h : ∀ i, (↑F : _ →+ R).comp (of A i) = (↑G : _ →+ R).comp (of A i)) : F = G :=
ring_hom.coe_add_monoid_hom_injective $ direct_sum.add_hom_ext' h

/-- Two `ring_hom`s out of a direct sum are equal if they agree on the generators. -/
lemma ring_hom_ext ⦃f g : (⨁ i, A i) →+* R⦄ (h : ∀ i x, f (of A i x) = g (of A i x)) :
  f = g :=
ring_hom_ext' $ λ i, add_monoid_hom.ext $ h i

/-- A family of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
describes a `ring_hom`s on `⨁ i, A i`. This is a stronger version of `direct_sum.to_monoid`.

Of particular interest is the case when `A i` are bundled subojects, `f` is the family of
coercions such as `add_submonoid.subtype (A i)`, and the `[gsemiring A]` structure originates from
`direct_sum.gsemiring.of_add_submonoids`, in which case the proofs about `ghas_one` and `ghas_mul`
can be discharged by `rfl`. -/
@[simps]
def to_semiring
  (f : Π i, A i →+ R) (hone : f _ (graded_monoid.ghas_one.one) = 1)
  (hmul : ∀ {i j} (ai : A i) (aj : A j), f _ (graded_monoid.ghas_mul.mul ai aj) = f _ ai * f _ aj) :
  (⨁ i, A i) →+* R :=
{ to_fun := to_add_monoid f,
  map_one' := begin
    change (to_add_monoid f) (of _ 0 _) = 1,
    rw to_add_monoid_of,
    exact hone
  end,
  map_mul' := begin
    rw (to_add_monoid f).map_mul_iff,
    ext xi xv yi yv : 4,
    show to_add_monoid f (of A xi xv * of A yi yv) =
         to_add_monoid f (of A xi xv) * to_add_monoid f (of A yi yv),
    rw [of_mul_of, to_add_monoid_of, to_add_monoid_of, to_add_monoid_of],
    exact hmul _ _,
  end,
  .. to_add_monoid f}

@[simp] lemma to_semiring_of (f : Π i, A i →+ R) (hone hmul) (i : ι) (x : A i) :
  to_semiring f hone hmul (of _ i x) = f _ x :=
to_add_monoid_of f i x

@[simp] lemma to_semiring_coe_add_monoid_hom (f : Π i, A i →+ R) (hone hmul):
  (to_semiring f hone hmul : (⨁ i, A i) →+ R) = to_add_monoid f := rfl

/-- Families of `add_monoid_hom`s preserving `direct_sum.ghas_one.one` and `direct_sum.ghas_mul.mul`
are isomorphic to `ring_hom`s on `⨁ i, A i`. This is a stronger version of `dfinsupp.lift_add_hom`.
-/
@[simps]
def lift_ring_hom :
  {f : Π {i}, A i →+ R //
    f (graded_monoid.ghas_one.one) = 1 ∧
    ∀ {i j} (ai : A i) (aj : A j), f (graded_monoid.ghas_mul.mul ai aj) = f ai * f aj} ≃
    ((⨁ i, A i) →+* R) :=
{ to_fun := λ f, to_semiring f.1 f.2.1 f.2.2,
  inv_fun := λ F,
    ⟨λ i, (F : (⨁ i, A i) →+ R).comp (of _ i), begin
      simp only [add_monoid_hom.comp_apply, ring_hom.coe_add_monoid_hom],
      rw ←F.map_one,
      refl
    end, λ i j ai aj, begin
      simp only [add_monoid_hom.comp_apply, ring_hom.coe_add_monoid_hom],
      rw [←F.map_mul, of_mul_of],
    end⟩,
  left_inv := λ f, begin
    ext xi xv,
    exact to_add_monoid_of f.1 xi xv,
  end,
  right_inv := λ F, begin
    apply ring_hom.coe_add_monoid_hom_injective,
    ext xi xv,
    simp only [ring_hom.coe_add_monoid_hom_mk,
      direct_sum.to_add_monoid_of,
      add_monoid_hom.mk_coe,
      add_monoid_hom.comp_apply, to_semiring_coe_add_monoid_hom],
  end}

end to_semiring

end direct_sum

/-! ### Concrete instances -/

section uniform

variables (ι)

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring
  {R : Type*} [add_monoid ι] [non_unital_non_assoc_semiring R] :
  direct_sum.gnon_unital_non_assoc_semiring (λ i : ι, R) :=
{ mul_zero := λ i j, mul_zero,
  zero_mul := λ i j, zero_mul,
  mul_add := λ i j, mul_add,
  add_mul := λ i j, add_mul,
  ..has_mul.ghas_mul ι }

/-- A direct sum of copies of a `semiring` inherits the multiplication structure. -/
instance semiring.direct_sum_gsemiring {R : Type*} [add_monoid ι] [semiring R] :
  direct_sum.gsemiring (λ i : ι, R) :=
{ nat_cast := λ n, n,
  nat_cast_zero := nat.cast_zero,
  nat_cast_succ := nat.cast_succ,
  ..non_unital_non_assoc_semiring.direct_sum_gnon_unital_non_assoc_semiring ι,
  ..monoid.gmonoid ι }

open_locale direct_sum

-- To check `has_mul.ghas_mul_mul` matches
example {R : Type*} [add_monoid ι] [semiring R] (i j : ι) (a b : R) :
  (direct_sum.of _ i a * direct_sum.of _ j b : ⨁ i, R) = direct_sum.of _ (i + j) (by exact a * b) :=
by rw [direct_sum.of_mul_of, has_mul.ghas_mul_mul]

/-- A direct sum of copies of a `comm_semiring` inherits the commutative multiplication structure.
-/
instance comm_semiring.direct_sum_gcomm_semiring {R : Type*} [add_comm_monoid ι] [comm_semiring R] :
  direct_sum.gcomm_semiring (λ i : ι, R) :=
{ ..comm_monoid.gcomm_monoid ι, ..semiring.direct_sum_gsemiring ι }

end uniform
