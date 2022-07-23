import cicm2022.internal.decomposition
import cicm2022.internal.graded_ring

section ghas_smul
-- External version of graded scalar multiplication

variables {ι : Type*} (A : ι → Type*) (M : ι → Type*)
/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class ghas_smul [has_add ι] :=
(smul {i j} : A i → M j → M (i + j))

instance ghas_smul.to_has_smul [has_add ι] [ghas_smul A M] :
  has_smul (graded_monoid A) (graded_monoid M) :=
⟨λ (x : graded_monoid A) (y : graded_monoid M), ⟨_, ghas_smul.smul x.snd y.snd⟩⟩


end ghas_smul


section set_like
-- Internal version of graded scalar multiplication

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
  ghas_smul (λ i, A i) (λ i, B i) :=
{ smul := λ i j a b, ⟨(a : R) • b, set_like.has_graded_smul.smul_mem a.2 b.2⟩ }

@[simp] lemma set_like.coe_ghas_smul {ι S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B]
  {i j : ι} (x : A i) (y : B j) :
  (@ghas_smul.smul ι (λ i, A i) (λ i, B i) _ _ i j x y : M) = ((x : R) • y) :=
rfl

/--
Every graded ring is trivially a graded module over itself
-/
instance set_like.graded_monoid.to_has_graded_smul
   {ι S R : Type*} [set_like S R] [monoid R] [add_monoid ι] (A : ι → S) [set_like.graded_monoid A] :
   set_like.has_graded_smul A A :=
{ smul_mem := λ i j ai bj hi hj, set_like.graded_monoid.mul_mem hi hj, }

end set_like

-------------------------------- Graded Module ------------------------------------------------------

section gmodule
-- External version of graded module
open_locale direct_sum

variables {ι : Type*} [add_monoid ι] [decidable_eq ι] (A : ι → Type*) (M : ι → Type*)
variables [Π (i : ι), add_comm_monoid (A i)] [Π i, add_comm_monoid $ M i]

class gmul_action [graded_monoid.gmonoid A] extends ghas_smul A M :=
(one_smul (b : graded_monoid M) : (1 : graded_monoid A) • b = b)
(mul_smul (a a' : graded_monoid A) (b : graded_monoid M) : (a * a') • b = a • a' • b)

class gdistrib_mul_action [graded_monoid.gmonoid A] extends gmul_action A M :=
(smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c)
(smul_zero {i j} (a : A i) : smul a (0 : M j) = 0)

class gmodule [graded_monoid.gmonoid A] extends
  gdistrib_mul_action A M :=
(add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b)
(zero_smul {i j} (b : M j) : smul (0 : A i) b = 0)

def gmodule.smul_add_monoid_hom
  [graded_monoid.gmonoid A] [gmodule A M] :
  (⨁ i, A i) →+ (⨁ i, M i) →+ (⨁ i, M i) :=
direct_sum.to_add_monoid $ λ i,
{ to_fun := λ a, direct_sum.to_add_monoid $ λ j,
  { to_fun := λ b, direct_sum.of _ (i + j) (ghas_smul.smul a b),
    map_zero' :=
    begin
      convert map_zero _,
      apply gdistrib_mul_action.smul_zero,
    end,
    map_add' := λ x y,
    begin
      convert map_add _ _ _,
      apply gdistrib_mul_action.smul_add,
    end },
  map_zero' := fun_like.ext _ _ $ λ x,
  begin
    rw [add_monoid_hom.zero_apply],
    induction x using direct_sum.induction_on with j y y₁ y₂ ih₁ ih₂,
    { convert map_zero _, },
    { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
      convert map_zero _,
      apply gmodule.zero_smul, },
    { rw [map_add, ih₁, ih₂, zero_add], },
  end,
  map_add' := λ a₁ a₂, fun_like.ext _ _ $ λ y,
  begin
    induction y using direct_sum.induction_on with j y y₁ y₂ ih₁ ih₂,
    { rw [map_zero, map_zero] },
    { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk, add_monoid_hom.add_apply],
      rw [←map_add],
      congr,
      apply gmodule.add_smul, },
    { simp only [map_add, ih₁, ih₂] },
  end }

section

variables [graded_monoid.gmonoid A] [gmodule A M]
instance : has_smul (⨁ i, A i) (⨁ i, M i) :=
{ smul := λ x y, gmodule.smul_add_monoid_hom A M x y }

@[simp] lemma gmodule.smul_def
  (x : ⨁ i, A i) (y : ⨁ i, M i) : x • y = gmodule.smul_add_monoid_hom _ _ x y := rfl
@[simp] lemma gmodule.smul_add_monoid_hom_apply_of_of {i j} (x : A i) (y : M j) :
  gmodule.smul_add_monoid_hom A M (direct_sum.of A i x) (direct_sum.of M j y) =
  direct_sum.of M (i + j) (ghas_smul.smul x y) :=
by simp [gmodule.smul_add_monoid_hom]

@[simp] lemma gmodule.of_smul_of
  {i j} (x : A i) (y : M j) :
  direct_sum.of A i x • direct_sum.of M j y =
  direct_sum.of M (i + j) (ghas_smul.smul x y) :=
by rw [gmodule.smul_def, gmodule.smul_add_monoid_hom, direct_sum.to_add_monoid_of,
    add_monoid_hom.coe_mk, direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk]

end

instance gmodule.module [direct_sum.gsemiring A] [gmodule A M] : module (⨁ i, A i) (⨁ i, M i) :=
{ smul := (•),
  one_smul :=
  begin
    intros b,
    induction b using direct_sum.induction_on with j b x₁ x₂ ih₁ ih₂,
    { simp, },
    { rw [show (1 : ⨁ i, A i) = direct_sum.of _ _ _, from rfl, gmodule.of_smul_of],
      apply direct_sum.of_eq_of_graded_monoid_eq,
      exact gmul_action.one_smul (⟨_, b⟩ : graded_monoid M) },
    { simp only [gmodule.smul_def] at ih₁ ih₂,
      simp only [gmodule.smul_def, map_add, ih₁, ih₂], },
  end,
  mul_smul := λ x y z,
  begin
    rw [gmodule.smul_def, gmodule.smul_def, gmodule.smul_def],
    induction x using direct_sum.induction_on with i x x₁ x₂ ihx₁ ihx₂,
    { rw [zero_mul, map_zero, add_monoid_hom.zero_apply, add_monoid_hom.zero_apply], },
    { induction y using direct_sum.induction_on with j y y₁ y₂ ihy₁ ihy₂,
      { rw [mul_zero, map_zero, add_monoid_hom.zero_apply, map_zero], },
      { simp only [direct_sum.of_mul_of, gmodule.smul_add_monoid_hom,
          direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
        induction z using direct_sum.induction_on with k z z₁ z₂ ihz₁ ihz₂,
        { rw [map_zero, map_zero, map_zero], },
        { simp only [direct_sum.to_add_monoid_of, add_monoid_hom.coe_mk],
          apply direct_sum.of_eq_of_graded_monoid_eq,
          exact gmul_action.mul_smul ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩, },
        { simp only [map_add, ihz₁, ihz₂], }, },
      { simp only [map_add, ←ihy₁, ←ihy₂, add_monoid_hom.add_apply],
        simp_rw [mul_add, map_add],
        simp only [add_monoid_hom.add_apply], }, },
    { simp only [add_mul, map_add, ihx₁, ihx₂, add_monoid_hom.add_apply], },
  end,
  smul_add := λ r x y,
  begin
    induction r using direct_sum.induction_on with i r r₁ r₂ ihr₁ ihr₂,
    { simp only [gmodule.smul_def, map_zero, add_monoid_hom.zero_apply, add_zero], },
    { simp only [gmodule.smul_def, map_add] },
    { simp only [gmodule.smul_def] at ihr₁ ihr₂ ⊢,
      simp only [map_add, ihr₁, ihr₂], },
  end,
  smul_zero := λ r, by simp only [gmodule.smul_def, map_zero],
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

variables [add_comm_monoid M] [module A M] [set_like σ M] [add_submonoid_class σ' A]
  [add_submonoid_class σ M] [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜]

-- [set_like.graded_monoid 𝓐] [set_like.has_graded_smul 𝓐 𝓜] is the internal version of graded module
-- the internal version can be translated into the external version `gmodule`.
instance gmodule [decidable_eq ι] : gmodule (λ i, 𝓐 i) (λ i, 𝓜 i) :=
{ smul := λ i j x y, ⟨(x : A) • (y : M), set_like.has_graded_smul.smul_mem x.2 y.2⟩,
  one_smul := λ ⟨i, m⟩, sigma.subtype_ext (zero_add _) $ one_smul _ _,
  mul_smul := λ ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩, sigma.subtype_ext (add_assoc _ _ _) $ mul_smul _ _ _,
  smul_add := λ i j a b c, subtype.ext $ smul_add _ _ _,
  smul_zero := λ i j a, subtype.ext $ smul_zero _,
  add_smul := λ i j a a' b, subtype.ext $ add_smul _ _ _,
  zero_smul := λ i j b, subtype.ext $ zero_smul _ _ }


/--
Since `A ≃+ ⨁ i, 𝓐 i`, the `⨁ i, 𝓐 i`-module structure on `⨁ i, 𝓜 i` also defines a module
structure as an `A`-module.
-/
instance [decidable_eq ι] [graded_ring 𝓐] : module A (⨁ i, 𝓜 i) :=
module.comp_hom (⨁ i, 𝓜 i) (direct_sum.decompose_ring_equiv 𝓐 : A →+* ⨁ i, 𝓐 i)

/--
`⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
-/
def linear_equiv [decidable_eq ι] [graded_ring 𝓐] [set_like.has_graded_smul 𝓐 𝓜]
  [direct_sum.decomposition 𝓜] :
  M ≃ₗ[A] ⨁ i, 𝓜 i :=
{ to_fun := direct_sum.decompose_add_equiv 𝓜,
  map_add' := λ x y, map_add _ _ _,
  map_smul' := λ x y, begin
    rw [ring_hom.id_apply],
    let 𝓜' : ι → add_submonoid M :=
      λ i, (⟨𝓜 i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid M),
    haveI t : direct_sum.decomposition 𝓜' :=
    { decompose' := direct_sum.decompose 𝓜,
      left_inv := λ _, (direct_sum.decompose 𝓜).left_inv _,
      right_inv := λ _, (direct_sum.decompose 𝓜).right_inv _, },
    have mem1 : ∀ m, m ∈ supr 𝓜' :=
      λ m, (direct_sum.is_internal.add_submonoid_supr_eq_top 𝓜'
        (direct_sum.decomposition.is_internal 𝓜')).symm ▸ trivial,

    let 𝓐' : ι → add_submonoid A :=
      λ i, (⟨𝓐 i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid A),
    haveI t : direct_sum.decomposition 𝓐' :=
    { decompose' := direct_sum.decompose 𝓐,
      left_inv := λ _, (direct_sum.decompose 𝓐).left_inv _,
      right_inv := λ _, (direct_sum.decompose 𝓐).right_inv _, },
    have mem2 : ∀ m, m ∈ supr 𝓐' :=
      λ m, (direct_sum.is_internal.add_submonoid_supr_eq_top 𝓐'
        (direct_sum.decomposition.is_internal 𝓐')).symm ▸ trivial,
    refine add_submonoid.supr_induction 𝓐' (mem2 x) _ _ _,
    { intros i a ha,
      rw [direct_sum.decompose_add_equiv_apply],
      refine add_submonoid.supr_induction 𝓜' (mem1 y) _ _ _,
      { intros j m hm,
        lift a to (𝓐 i) using ha,
        lift m to (𝓜 j) using hm,
        change _ = direct_sum.decompose _ _ • _,
        rw [direct_sum.decompose_coe, direct_sum.decompose_coe, gmodule.of_smul_of,
          show (a : A) • (m : M) = (↑(⟨(a : A) • (m : M),
            set_like.has_graded_smul.smul_mem a.2 m.2⟩ : 𝓜 (i + j)) : M), from rfl,
          direct_sum.decompose_coe],
        exact direct_sum.of_eq_of_graded_monoid_eq rfl, },
      { rw [smul_zero, direct_sum.decompose_zero, smul_zero], },
      { intros m₁ m₂ ih₁ ih₂,
        simp only [smul_add, direct_sum.decompose_add, ih₁, ih₂], }, },
    { simp only [zero_smul, map_zero] },
    { intros a₁ a₂ ih₁ ih₂,
      simp only [add_smul, ih₁, ih₂, map_add], },
  end,
  inv_fun := (direct_sum.decompose_add_equiv 𝓜).symm,
  left_inv := add_equiv.apply_symm_apply _,
  right_inv := add_equiv.symm_apply_apply _ }

end graded_module

end