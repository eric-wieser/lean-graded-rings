/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser

From: https://github.com/leanprover-community/mathlib/pull/14582
-/

import cicm2022.internal.decomposition
import cicm2022.internal.graded_ring

/-! # Graded scalar multiplication -/


/-! ### External version on graded monoid -/

namespace graded_monoid

variables {ι : Type*} (A : ι → Type*) (M : ι → Type*)

/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class ghas_smul [has_add ι] :=
(smul {i j} : A i → M j → M (i + j))

instance ghas_mul.to_ghas_mul [has_add ι] [ghas_mul A] : ghas_smul A A :=
{ smul := λ _ _, ghas_mul.mul }

instance [has_add ι] [ghas_smul A M] : has_smul (graded_monoid A) (graded_monoid M) :=
⟨λ (x : graded_monoid A) (y : graded_monoid M), ⟨_, ghas_smul.smul x.snd y.snd⟩⟩

/-- A graded version of `mul_action`. -/
class gmul_action [add_monoid ι] [graded_monoid.gmonoid A] extends ghas_smul A M :=
(one_smul (b : graded_monoid M) : (1 : graded_monoid A) • b = b)
(mul_smul (a a' : graded_monoid A) (b : graded_monoid M) : (a * a') • b = a • a' • b)

instance gmonoid.to_gmul_action [add_monoid ι] [gmonoid A] :
  gmul_action A A :=
{ one_smul := λ x, graded_monoid.gmonoid.one_mul x,
  mul_smul := graded_monoid.gmonoid.mul_assoc }

instance [add_monoid ι] [gmonoid A] [gmul_action A M] :
  mul_action (graded_monoid A) (graded_monoid M) :=
{ one_smul := gmul_action.one_smul,
  mul_smul := gmul_action.mul_smul }

end graded_monoid

/-! ### Internal version -/

section set_like

/-- A version of `graded_monoid.ghas_smul` for internally graded objects. -/
class set_like.has_graded_smul {ι S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) : Prop :=
(smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j))

lemma set_like.smul_mem_graded {ι S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B]
  ⦃i j⦄ {gi gj} (hi : gi ∈ A i) (hj : gj ∈ B j) :
  gi • gj ∈ B (i + j) :=
set_like.has_graded_smul.smul_mem hi hj

instance set_like.ghas_smul {ι S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B] :
  graded_monoid.ghas_smul (λ i, A i) (λ i, B i) :=
{ smul := λ i j a b, ⟨(a : R) • b, set_like.has_graded_smul.smul_mem a.2 b.2⟩ }

@[simp] lemma set_like.coe_ghas_smul {ι S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B]
  {i j : ι} (x : A i) (y : B j) :
  (@graded_monoid.ghas_smul.smul ι (λ i, A i) (λ i, B i) _ _ i j x y : M) = ((x : R) • y) :=
rfl

instance set_like.has_graded_mul.to_has_graded_smul
  {ι S R : Type*} [set_like S R] [monoid R] [add_monoid ι] (A : ι → S) [set_like.has_graded_mul A] :
  set_like.has_graded_smul A A :=
{ smul_mem := λ i j ai bj hi hj, set_like.has_graded_mul.mul_mem hi hj, }

end set_like

/-! ### Graded modules -/

section gmodule

section defs

variables {ι : Type*} [add_monoid ι] (A : ι → Type*) (M : ι → Type*)

/-- A graded version of `distrib_mul_action`. -/
class gdistrib_mul_action [graded_monoid.gmonoid A] [Π i, add_monoid $ M i]
  extends graded_monoid.gmul_action A M :=
(smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c)
(smul_zero {i j} (a : A i) : smul a (0 : M j) = 0)

/-- A graded version of `module`. -/
class gmodule [graded_monoid.gmonoid A] [Π i, add_comm_monoid $ M i] [Π i, add_comm_monoid $ A i]
  extends gdistrib_mul_action A M :=
(add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b)
(zero_smul {i j} (b : M j) : smul (0 : A i) b = 0)

end defs

-- External version of graded module
open_locale direct_sum

variables {ι : Type*} [add_monoid ι] (A : ι → Type*) (M : ι → Type*)
variables [Π (i : ι), add_comm_monoid (A i)] [Π i, add_comm_monoid $ M i]

/-- The piecewise multiplication from the `has_mul` instance, as a bundled homomorphism. -/
@[simps]
def gsmul_hom {i j} [graded_monoid.gmonoid A] [gmodule A M] : A i →+ M j →+ M (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, graded_monoid.ghas_smul.smul a b,
    map_zero' := gdistrib_mul_action.smul_zero _,
    map_add' := gdistrib_mul_action.smul_add _ },
  map_zero' := add_monoid_hom.ext $ λ a, gmodule.zero_smul a,
  map_add' := λ a₁ a₂, add_monoid_hom.ext $ λ b, gmodule.add_smul _ _ _}

/-- The multiplication from the `has_smul` instance, as a bundled homomorphism. -/
def gmodule.smul_add_monoid_hom [decidable_eq ι] [graded_monoid.gmonoid A] [gmodule A M] :
  (⨁ i, A i) →+ (⨁ i, M i) →+ ⨁ i, M i :=
direct_sum.to_add_monoid $ λ i,
  add_monoid_hom.flip $ direct_sum.to_add_monoid $ λ j, add_monoid_hom.flip $
    (direct_sum.of M _).comp_hom.comp $ gsmul_hom A M

section

variables [decidable_eq ι] [graded_monoid.gmonoid A] [gmodule A M]
instance : has_smul (⨁ i, A i) (⨁ i, M i) :=
{ smul := λ x y, gmodule.smul_add_monoid_hom A M x y }

@[simp] lemma gmodule.smul_def
  (x : ⨁ i, A i) (y : ⨁ i, M i) : x • y = gmodule.smul_add_monoid_hom _ _ x y := rfl
@[simp] lemma gmodule.smul_add_monoid_hom_apply_of_of {i j} (x : A i) (y : M j) :
  gmodule.smul_add_monoid_hom A M (direct_sum.of A i x) (direct_sum.of M j y) =
  direct_sum.of M (i + j) (graded_monoid.ghas_smul.smul x y) :=
by simp [gmodule.smul_add_monoid_hom]

@[simp] lemma gmodule.of_smul_of
  {i j} (x : A i) (y : M j) :
  direct_sum.of A i x • direct_sum.of M j y =
  direct_sum.of M (i + j) (graded_monoid.ghas_smul.smul x y) :=
gmodule.smul_add_monoid_hom_apply_of_of _ _ _ _

end

open add_monoid_hom

-- Almost identical to the proof of `direct_sum.one_mul`
private lemma one_smul [decidable_eq ι] [direct_sum.gsemiring A] [gmodule A M] (x : ⨁ i, M i) :
  (1 : ⨁ i, A i) • x = x :=
suffices gmodule.smul_add_monoid_hom A M 1 = add_monoid_hom.id (⨁ i, M i),
  from add_monoid_hom.congr_fun this x,
begin
  apply direct_sum.add_hom_ext, intros i xi,
  unfold has_one.one,
  rw gmodule.smul_add_monoid_hom_apply_of_of,
  exact direct_sum.of_eq_of_graded_monoid_eq (one_smul (graded_monoid A) $ graded_monoid.mk i xi),
end

-- Almost identical to the proof of `direct_sum.mul_assoc`
private lemma mul_smul [decidable_eq ι] [direct_sum.gsemiring A] [gmodule A M]
  (a b : ⨁ i, A i) (c : ⨁ i, M i) : (a * b) • c = a • (b • c) :=
suffices (gmodule.smul_add_monoid_hom A M).comp_hom.comp (direct_sum.mul_hom A) -- `λ a b c, (a * b) • c` as a bundled hom
       = (add_monoid_hom.comp_hom add_monoid_hom.flip_hom $                     -- `λ a b c, a • (b • c)` as a bundled hom
             (gmodule.smul_add_monoid_hom A M).flip.comp_hom.comp (gmodule.smul_add_monoid_hom A M)).flip,
  from add_monoid_hom.congr_fun (add_monoid_hom.congr_fun (add_monoid_hom.congr_fun this a) b) c,
begin
  ext ai ax bi bx ci cx : 6,
  dsimp only [coe_comp, function.comp_app, comp_hom_apply_apply, flip_apply, flip_hom_apply],
  rw [gmodule.smul_add_monoid_hom_apply_of_of, gmodule.smul_add_monoid_hom_apply_of_of,
    direct_sum.mul_hom_of_of, gmodule.smul_add_monoid_hom_apply_of_of],
  exact direct_sum.of_eq_of_graded_monoid_eq
    (mul_smul (graded_monoid.mk ai ax) (graded_monoid.mk bi bx) (graded_monoid.mk ci cx)),
end

instance gmodule.module [decidable_eq ι] [direct_sum.gsemiring A] [gmodule A M] :
  module (⨁ i, A i) (⨁ i, M i) :=
{ smul := (•),
  one_smul := one_smul _ _,
  mul_smul := mul_smul _ _,
  smul_add := λ r, (gmodule.smul_add_monoid_hom A M r).map_add,
  smul_zero := λ r, (gmodule.smul_add_monoid_hom A M r).map_zero,
  add_smul := λ r s x, by simp only [gmodule.smul_def, map_add, add_monoid_hom.add_apply],
  zero_smul := λ x, by simp only [gmodule.smul_def, map_zero, add_monoid_hom.zero_apply] }

end gmodule

section

-- internal version of graded module

variables {ι R A M σ σ' : Type*}
variables [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝓐 : ι → σ') [set_like σ' A]
variables (𝓜 : ι → σ)

open_locale direct_sum

namespace graded_module

include σ' A σ M

instance gdistrib_mul_action [add_monoid M] [distrib_mul_action A M]
  [set_like σ M] [add_submonoid_class σ M] [set_like.graded_monoid 𝓐]
  [set_like.has_graded_smul 𝓐 𝓜] :
  gdistrib_mul_action (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul := λ i j x y, ⟨(x : A) • (y : M), set_like.has_graded_smul.smul_mem x.2 y.2⟩,
  one_smul := λ ⟨i, m⟩, sigma.subtype_ext (zero_add _) (one_smul _ _),
  mul_smul := λ ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩, sigma.subtype_ext (add_assoc _ _ _) (mul_smul _ _ _),
  smul_add := λ i j a b c, subtype.ext $ smul_add _ _ _,
  smul_zero := λ i j a, subtype.ext $ smul_zero _ }

variables [add_comm_monoid M] [module A M] [set_like σ M] [add_submonoid_class σ' A]
  [add_submonoid_class σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]

-- [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜] is the internal version of graded module
-- the internal version can be translated into the external version `gmodule`.
instance gmodule : gmodule (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul := λ i j x y, ⟨(x : A) • (y : M), set_like.has_graded_smul.smul_mem x.2 y.2⟩,
  add_smul := λ i j a a' b, subtype.ext $ add_smul _ _ _,
  zero_smul := λ i j b, subtype.ext $ zero_smul _ _,
  ..graded_module.gdistrib_mul_action 𝓐 𝓜}

/--
The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
def is_module [decidable_eq ι] [graded_ring 𝓐] :
  module A (⨁ i, 𝓜 i) :=
{ smul := λ a b, direct_sum.decompose 𝓐 a • b,
  ..module.comp_hom _ $
    (direct_sum.decompose_ring_equiv 𝓐 : A ≃+* ⨁ i, 𝓐 i).to_ring_hom }

local attribute [instance] graded_module.is_module

/--
`⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules.
-/
def linear_equiv [decidable_eq ι] [graded_ring 𝓐] 
  [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_smul' := λ x y, begin
    classical,
    rw [← direct_sum.sum_support_decompose 𝓐 x, map_sum, finset.sum_smul, map_sum,
      finset.sum_smul, finset.sum_congr rfl (λ i hi, _)],
    rw [ring_hom.id_apply, ← direct_sum.sum_support_decompose 𝓜 y, map_sum, finset.smul_sum,
      map_sum, finset.smul_sum, finset.sum_congr rfl (λ j hj, _)],
    unfold has_smul.smul,
    simp only [direct_sum.decompose_add_equiv_apply, direct_sum.decompose_coe,
      gmodule.smul_add_monoid_hom_apply_of_of],
    convert direct_sum.decompose_coe 𝓜 _,
    refl,
  end,
  .. (direct_sum.decompose_add_equiv 𝓜) }

end graded_module

end
