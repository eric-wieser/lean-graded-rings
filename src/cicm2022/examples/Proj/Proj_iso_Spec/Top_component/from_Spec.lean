import cicm2022.examples.Proj.degree_zero_part
import cicm2022.examples.Proj.structure_sheaf
import cicm2022.examples.Proj.lemmas
import cicm2022.examples.Proj.radical
import cicm2022.examples.Proj.Proj_iso_Spec.Top_component.to_Spec

import algebraic_geometry.structure_sheaf
import algebraic_geometry.Spec

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

namespace Proj_iso_Spec_Top_component

namespace from_Spec

open graded_algebra finset (hiding mk_zero)
variable {𝒜}

variables {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}

/--The underlying set-/
def carrier (q : Spec.T (A⁰_ f_deg)) : set A :=
{a | ∀ i, (⟨mk ((proj 𝒜 i a)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1}

lemma mem_carrier_iff (q : Spec.T (A⁰_ f_deg)) (a : A) :
  a ∈ carrier q ↔ ∀ i, (⟨mk ((proj 𝒜 i a)^m) ⟨_, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 := iff.rfl

lemma carrier.zero_mem (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  (0 : A) ∈ carrier q := λ i,
by simpa only [linear_map.map_zero, zero_pow hm, mk_zero] using submodule.zero_mem _

lemma carrier.add_mem (q : Spec.T (A⁰_ f_deg)) {a b : A}
  (ha : a ∈ carrier q) (hb : b ∈ carrier q) :
  a + b ∈ carrier q :=
begin
  rw carrier at ha hb ⊢,
  intro i,
  set α := (⟨mk ((proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg),
  suffices : α * α ∈ q.1,
  { cases q.2.mem_or_mem this, assumption, assumption },
  { rw show α * α =
    ⟨mk ((proj 𝒜 i (a + b))^(2*m)) ⟨f^(2*i), ⟨_, rfl⟩⟩,
      ⟨2 * i, ⟨_, by { rw show m * (2 * i) = (2 * m) * i, by ring, exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _) }⟩, rfl⟩⟩,
    { rw [subtype.ext_iff, subring.coe_mul, subtype.coe_mk, mk_mul],
      congr' 1,
      { rw [two_mul, pow_add] },
      { simp only [subtype.ext_iff, submonoid.coe_mul, ← subtype.val_eq_coe, two_mul, pow_add],
        refl, } },
      clear α,

      set s := ∑ j in range (2 * m + 1), ((proj 𝒜 i) a)^j * ((proj 𝒜 i) b)^(2 * m - j) * (2 * m).choose j,
      set s' := ∑ j in (range (2*m + 1)).attach, (proj 𝒜 i a)^j.1 * (proj 𝒜 i b)^(2 * m - j.1) * (2 * m).choose j.1,
      have ss' : s = s',
      { change finset.sum _ _ = finset.sum _ _,
        simp_rw [subtype.val_eq_coe],
        symmetry,
        convert sum_attach,
        refl, },
      have mem1 : (proj 𝒜 i) (a + b) ^ (2 * m) ∈ 𝒜 (m * (2 * i)),
      { rw show m * (2 * i) = (2 * m) * i, by ring, exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _) },
      have eq1 : (proj 𝒜 i (a + b))^(2*m) = s,
      { rw [linear_map.map_add, add_pow] },
      rw calc (⟨mk ((proj 𝒜 i (a + b))^(2*m)) ⟨f^(2*i), ⟨_, rfl⟩⟩, ⟨2 * i, ⟨_, mem1⟩, rfl⟩⟩ : A⁰_ f_deg)
            = ⟨mk s ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, ⟨2*i, ⟨s, eq1 ▸ mem1⟩, rfl⟩⟩
            : begin
              erw [subtype.ext_iff_val],
              dsimp only,
              erw [linear_map.map_add, add_pow],
            end
        ... = ⟨mk s' ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, ⟨2*i, ⟨s', ss' ▸ eq1 ▸ mem1⟩, rfl⟩⟩ : by congr' 2
        ... = ∑ j in (range (2 * m + 1)).attach,
                ⟨mk ((proj 𝒜 i a)^j.1 * (proj 𝒜 i b)^(2 * m - j.1) * (2 * m).choose j.1) ⟨f^(2 * i), ⟨2*i, rfl⟩⟩,
                ⟨2*i, ⟨_, begin
                  have mem1 : (proj 𝒜 i) a ^ j.1 ∈ 𝒜 (j.1 * i),
                  { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _), },
                  have mem2 : (proj 𝒜 i) b ^ (2 * m - j.1) ∈ 𝒜 ((2*m-j.1) * i),
                  { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _) },
                  have mem3 : ((2 * m).choose j.1 : A) ∈ 𝒜 0,
                  { exact set_like.has_graded_one.nat_cast_mem _ _, },
                  rw show m * (2 * i) = ((j.1*i) + (2*m-j.1)*i + 0),
                  { zify,
                    rw [show (↑(2 * m - j.1) : ℤ) = 2 * m - j.1,
                    { rw [eq_sub_iff_add_eq, ←int.coe_nat_add, nat.sub_add_cancel (nat.lt_succ_iff.mp (mem_range.mp j.2))],
                      refl, }, sub_mul, add_zero],
                    ring, },
                  apply set_like.graded_monoid.mul_mem _ mem3,
                  apply set_like.graded_monoid.mul_mem mem1 mem2,
                end⟩, rfl⟩⟩
            : by simp only [subtype.ext_iff, subtype.coe_mk, add_submonoid_class.coe_finset_sum, localization.mk_sum],
      clear' s s' ss' eq1,
      apply ideal.sum_mem,
      intros k hk,
      by_cases ineq : m ≤ k.1,
      { -- use (proj 𝒜 i) a ^ k
        set α := (⟨mk ((proj 𝒜 i) a ^ m) ⟨f^i, ⟨i, rfl⟩⟩, ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg),
        set β := (⟨mk ((proj 𝒜 i) a ^ (k.val - m) *
            (proj 𝒜 i) b ^ (2 * m - k.val) * (2*m).choose k.1) ⟨f^i, ⟨i, rfl⟩⟩, begin
              refine ⟨i, ⟨_, _⟩, rfl⟩,
              have mem1 : (proj 𝒜 i) a ^ (k.val - m) ∈ 𝒜 ((k.val - m) * i),
              { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _), },
              have mem2 : (proj 𝒜 i) b ^ (2 * m - k.val) ∈ 𝒜 ((2*m-k.1) * i),
              { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _), },
              have mem3 : ((2*m).choose k.1 : A) ∈ 𝒜 0,
              { exact set_like.has_graded_one.nat_cast_mem _ _, },
              rw show m * i = ((k.val - m) * i) + ((2*m-k.1) * i) + 0,
              { rw [add_zero, ←add_mul],
                congr' 1,
                symmetry,
                exact calc k.val - m + (2*m - k.val)
                          = (k.val + (2 * m - k.1)) - m : by { rw nat.sub_add_comm ineq, }
                      ... = (k.1 + 2 * m) - k.1 - m
                          : begin
                            rw ←nat.add_sub_assoc,
                            have hk := k.2,
                            rw [finset.mem_range, nat.lt_succ_iff] at hk,
                            exact hk,
                          end
                      ... = 2 * m - m : by { rw nat.add_sub_cancel_left k.1 (2*m), }
                      ... = m + m - m : by { rw two_mul, }
                      ... = m : by rw nat.add_sub_cancel, },
              apply set_like.graded_monoid.mul_mem,
              apply set_like.graded_monoid.mul_mem,
              exact mem1, exact mem2, exact mem3,
            end⟩ : A⁰_ f_deg),
        suffices : α * β ∈ q.1,
        { convert this,
          rw [mk_mul],
          congr' 1,
          { simp only [← mul_assoc],
            congr' 2,
            rw [← pow_add],
            congr' 1,
          symmetry,
          exact calc m + (k.1 - m)
                    = m + k.1 - m : by erw ←nat.add_sub_assoc ineq
                ... = k.1 + m - m : by rw nat.add_comm
                ... = k.1 + (m-m) : by erw nat.add_sub_assoc (le_refl _)
                ... = k.1 + 0 : by rw nat.sub_self
                ... = k.1 : by rw add_zero },
          { simp only [two_mul, pow_add], refl, } },
        { apply ideal.mul_mem_right,
          apply ha, } },

      { set α := (⟨mk ((proj 𝒜 i) b ^ m) ⟨f^i, ⟨_, rfl⟩⟩, ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg),
        set β := (⟨mk ((proj 𝒜 i) a ^ k.val * (proj 𝒜 i) b ^ (m - k.val) * ((2 * m).choose k.val))
          ⟨f^i, ⟨_, rfl⟩⟩, begin
            have mem1 : (proj 𝒜 i) a ^ k.val ∈ 𝒜 (k.1 * i),
            { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _), },
            have mem2 : (graded_algebra.proj 𝒜 i) b ^ (m - k.val) ∈ 𝒜 ((m - k.1) * i),
            { exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _), },
            have mem3 : ↑((2 * m).choose k.val) ∈ 𝒜 0,
            { apply set_like.has_graded_one.nat_cast_mem, },
            refine ⟨_, ⟨_, _⟩, rfl⟩,
            rw ← show k.1 * i + (m - k.1) * i + 0 = m * i,
            { exact calc k.1 * i + (m - k.1) * i + 0
                      = k.1 * i + (m - k.1) * i : by { rw add_zero }
                  ... = (k.1 + (m - k.1)) * i : by { rw add_mul, }
                  ... = (k.1 + m - k.1) * i
                        : begin
                          rw nat.add_sub_assoc,
                          rw not_le at ineq,
                          apply le_of_lt,
                          exact ineq,
                        end
                  ... = m * i : by rw nat.add_sub_cancel_left, },
            apply set_like.graded_monoid.mul_mem,
            apply set_like.graded_monoid.mul_mem,
            exact mem1, exact mem2, exact mem3,
          end⟩ : A⁰_ f_deg),
        suffices : α * β ∈ q.1,
        { convert this,
          rw [localization.mk_mul],
          congr' 1,
          { simp only [← mul_assoc],
            congr' 1,
            conv_rhs { rw [mul_comm _ (proj 𝒜 i a ^ k.1), mul_assoc] },
            congr' 1,
            simp only [← pow_add],
            congr' 1,
            rw [← nat.add_sub_assoc],
            congr' 1,
            rw [two_mul],
            rw not_le at ineq,
            apply le_of_lt,
            exact ineq, },
          { simp only [two_mul, pow_add],
            refl, } },
        { apply ideal.mul_mem_right,
          apply hb, } }, },
end

lemma carrier.smul_mem (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) (c x : A) (hx : x ∈ carrier q) :
  c • x ∈ carrier q :=
begin
  classical,
  let 𝒜' : ℕ → add_submonoid A := λ i, (𝒜 i).to_add_submonoid,
  letI : graded_ring 𝒜' :=
    { decompose' := (direct_sum.decompose 𝒜 : A → ⨁ i, 𝒜 i),
      left_inv := direct_sum.decomposition.left_inv,
      right_inv := direct_sum.decomposition.right_inv,
      ..(by apply_instance : set_like.graded_monoid 𝒜), },
  have mem_supr : ∀ x, x ∈ supr 𝒜',
  { intro x,
    rw direct_sum.is_internal.add_submonoid_supr_eq_top 𝒜'
      (direct_sum.decomposition.is_internal 𝒜'),
    exact add_submonoid.mem_top x },
  
  refine add_submonoid.supr_induction 𝒜' (mem_supr c) (λ n a ha, _) _ _,
  { intros i,
    by_cases ineq1 : n ≤ i,
    { have eq1 : (graded_algebra.proj 𝒜 i) (a * x) =
          ite (i - n ∈ (direct_sum.decompose_alg_equiv 𝒜 x).support) (a * (graded_algebra.proj 𝒜 (i - n)) x) 0,
      { exact calc (proj 𝒜 i) (a * x)
              = proj 𝒜 i ∑ j in (direct_sum.decompose_alg_equiv 𝒜 x).support, (a * (proj 𝒜 j x))
              : begin
                conv_lhs { rw [← sum_support_decompose 𝒜 x] },
                simp_rw [proj_apply],
                rw [finset.mul_sum],
                refl,
              end
          ... = ∑ j in (direct_sum.decompose_alg_equiv 𝒜 x).support, (proj 𝒜 i (a * (proj 𝒜 j x)))
              : by rw linear_map.map_sum
          ... = ∑ j in (direct_sum.decompose_alg_equiv 𝒜 x).support, (ite (j = i - n) (proj 𝒜 i (a * (proj 𝒜 j x))) 0)
              : begin
                rw finset.sum_congr rfl,
                intros j hj,
                symmetry,
                split_ifs with H,
                refl,
                symmetry,
                have mem1 : a * graded_algebra.proj 𝒜 j x ∈ 𝒜 (n + j),
                { exact mul_mem ha (submodule.coe_mem _), },
                rw graded_algebra.proj_apply,
                apply direct_sum.decompose_of_mem_ne 𝒜 mem1,
                intro rid,
                rw [←rid, add_comm, nat.add_sub_assoc, nat.sub_self, add_zero] at H,
                apply H, refl, refl,
              end
          ... = ∑ j in (direct_sum.decompose_alg_equiv 𝒜 x).support,
                (ite (j = i - n) (a * (graded_algebra.proj 𝒜 j x)) 0)
              : begin
                rw finset.sum_congr rfl,
                intros j hj,
                split_ifs with eq1 ineq1,
                rw [graded_algebra.proj_apply, graded_algebra.proj_apply],
                apply direct_sum.decompose_of_mem_same,
                rw ←graded_algebra.proj_apply,
                have eq2 : i = j + n,
                { rw [eq1, nat.sub_add_cancel], exact ineq1, },
                rw [eq2, add_comm],
                apply set_like.graded_monoid.mul_mem ha (submodule.coe_mem _),
                refl,
              end
          ... = ite (i - n ∈ (direct_sum.decompose_alg_equiv 𝒜 x).support) (a * (proj 𝒜 (i - n)) x) 0 : by rw finset.sum_ite_eq', },

      split_ifs at eq1,
      { generalize_proofs h1 h2,
        erw calc
                (⟨mk ((proj 𝒜 i) (a * x) ^ m) ⟨f ^ i, h1⟩, h2⟩ : A⁰_ f_deg)
              = (⟨mk ((a * (proj 𝒜 (i - n) x))^m) ⟨f ^ i, h1⟩, eq1 ▸ h2⟩ : A⁰_ f_deg)
              : by { simp only [subtype.ext_iff_val, eq1], }
          ... = (⟨localization.mk ((a^m * (graded_algebra.proj 𝒜 (i - n) x)^m))
                  ⟨f^i, h1⟩, by { rw [←mul_pow, ←eq1], exact h2 }⟩ : A⁰_ f_deg)
              : begin
                rw subtype.ext_iff_val,
                dsimp only,
                rw mul_pow,
              end
          ... = (⟨mk (a^m) ⟨f^n, ⟨_, rfl⟩⟩, begin
                  refine ⟨n, ⟨a^m, _⟩, rfl⟩,
                  exact set_like.graded_monoid.pow_mem m ha,
                end⟩ : A⁰_ f_deg) *
                (⟨mk ((proj 𝒜 (i-n) x)^m) ⟨f^(i-n), ⟨_, rfl⟩⟩, begin
                  refine ⟨i-n, ⟨(proj 𝒜 (i-n) x)^m, _⟩, rfl⟩,
                  dsimp only,
                  exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _),
                end⟩ : A⁰_ f_deg)
              : begin
                rw [subtype.ext_iff, subring.coe_mul],
                dsimp only [subtype.coe_mk],
                rw [localization.mk_mul],
                congr',
                dsimp only,
                rw ←pow_add,
                congr',
                rw [←nat.add_sub_assoc, add_comm, nat.add_sub_assoc, nat.sub_self, add_zero],
                refl,
                exact ineq1,
              end,
        apply ideal.mul_mem_left,
        apply hx },
      { simp only [smul_eq_mul, eq1, zero_pow hm, localization.mk_zero],
        exact submodule.zero_mem _ } },
    { -- in this case, the left hand side is zero
      rw not_le at ineq1,
      convert submodule.zero_mem _,
      suffices : graded_algebra.proj 𝒜 i (a • x) = 0,
      erw [this, zero_pow hm, localization.mk_zero],

      rw [← sum_support_decompose 𝒜 x, smul_eq_mul, finset.mul_sum, linear_map.map_sum],
      simp_rw [←proj_apply],
      convert finset.sum_eq_zero _,
      intros j hj,
      rw [proj_apply],
      have mem1 : a * graded_algebra.proj 𝒜 j x ∈ 𝒜 (n + j),
      { exact set_like.graded_monoid.mul_mem ha (submodule.coe_mem _), },
      apply direct_sum.decompose_of_mem_ne 𝒜 mem1,

      suffices : i < n + j,
      symmetry,
      apply ne_of_lt this,

      exact lt_of_lt_of_le ineq1 (nat.le_add_right _ _), }, },
  { rw zero_smul,
    apply carrier.zero_mem,
    exact hm, },
  { intros a b ha hb,
    rw add_smul,
    apply carrier.add_mem q ha hb, },
end

def carrier.as_ideal (hm : 0 < m) (q : Spec.T (A⁰_ f_deg) ) :
  ideal A :=
{ carrier := carrier q,
  zero_mem' := carrier.zero_mem hm q,
  add_mem' := λ a b, carrier.add_mem q,
  smul_mem' := carrier.smul_mem hm q }

lemma carrier.as_ideal.homogeneous  (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  (carrier.as_ideal hm q).is_homogeneous 𝒜  :=
begin
  intros i a ha,
  rw ←graded_algebra.proj_apply,
  change (proj _ i a) ∈ carrier q,
  change a ∈ carrier q at ha,
  intros j,
  have := calc (⟨mk ((proj 𝒜 j (proj 𝒜 i a)) ^ m) ⟨f^j, ⟨_, rfl⟩⟩, ⟨j, ⟨_, by exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)
          = (⟨mk ((ite (j = i) (proj 𝒜 j a) 0)^m) ⟨f^j, ⟨_, rfl⟩⟩, begin
              refine ⟨j, ⟨((ite (j = i) (proj 𝒜 j a) 0)^m), _⟩, rfl⟩,
              have mem1 : ite (j = i) ((proj 𝒜 j) a) 0 ∈ 𝒜 j,
              { split_ifs,
                exact submodule.coe_mem _,
                exact zero_mem _ },
              exact set_like.graded_monoid.pow_mem m mem1,
            end⟩ : A⁰_ f_deg)
            : begin
              rw [subtype.ext_iff_val],
              dsimp only,
              congr',
              split_ifs with eq1,
              rw [graded_algebra.proj_apply, graded_algebra.proj_apply, eq1],
              apply direct_sum.decompose_of_mem_same,
              rw [←graded_algebra.proj_apply],
              exact submodule.coe_mem _,

              apply direct_sum.decompose_of_mem_ne 𝒜 (submodule.coe_mem _),
              symmetry, exact eq1,
            end
      ... = (⟨localization.mk ((ite (j = i) ((graded_algebra.proj 𝒜 j a)^m) 0))
            ⟨f^j, ⟨_, rfl⟩⟩, begin
              refine ⟨j, ⟨(ite (j = i) ((graded_algebra.proj 𝒜 j a)^m) 0), _⟩, rfl⟩,
              split_ifs,
              exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _),
              exact submodule.zero_mem _,
            end⟩ : A⁰_ f_deg)
            : begin
              rw [subtype.ext_iff_val],
              dsimp only,
              split_ifs, refl,
              rw zero_pow hm,
            end
      ... = ite (j = i)
            (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
              ⟨i, ⟨_, by exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)
            (0 : A⁰_ f_deg)
            : begin
              split_ifs with H,
              erw H,
              simp only [subtype.ext_iff_val, localization.mk_zero],
              refl,
            end,
    erw this,
    split_ifs with H,
    { apply ha, },
    { exact submodule.zero_mem _, },
end

def carrier.as_homogeneous_ideal (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) : homogeneous_ideal 𝒜 :=
⟨carrier.as_ideal hm q, carrier.as_ideal.homogeneous hm q⟩

lemma carrier.relevant (hm : 0 < m) (q : Spec.T (A⁰_ f_deg)) :
  ¬ homogeneous_ideal.irrelevant 𝒜 ≤ carrier.as_homogeneous_ideal hm q :=
begin
  intro rid,
  have mem1 : f ∉ carrier.as_ideal hm q,
  { intro rid2,
    specialize rid2 m,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    convert rid2,
    rw [subtype.ext_iff, subring.coe_one],
    dsimp only [subtype.coe_mk],
    symmetry,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
    convert localization.mk_self _,
    refl,
    exact f_deg },
  apply mem1,
  have mem2 : f ∈ homogeneous_ideal.irrelevant 𝒜,
  { change graded_algebra.proj 𝒜 0 f = 0,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 f_deg],
    symmetry,
    apply ne_of_lt,
    exact hm },
  apply rid mem2,
end

lemma carrier.as_ideal.prime (hm : 0 < m)
  (q : Spec.T (A⁰_ f_deg)) : (carrier.as_ideal hm q).is_prime :=
begin
  apply (carrier.as_ideal.homogeneous hm q).is_prime_of_homogeneous_mem_or_mem,
  { intro rid,
    rw ideal.eq_top_iff_one at rid,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    specialize rid 0,
    have eq1 : proj 𝒜 0 1 = 1,
    { rw [proj_apply, decompose_of_mem_same],
      exact one_mem, },
    simp only [eq1, one_pow] at rid,
    convert rid,
    rw [subtype.ext_iff, subring.coe_one],
    dsimp only [subtype.coe_mk],
    symmetry,
    convert localization.mk_one,
    rw pow_zero, },
  { -- homogeneously prime
    rintros x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy,
    contrapose hxy,
    rw not_or_distrib at hxy,
    rcases hxy with ⟨hx, hy⟩,
    change x ∉ carrier q at hx,
    change y ∉ carrier q at hy,
    change ¬ ∀ (i : ℕ),
      (⟨mk ((proj 𝒜 i x)^m) ⟨f^i, ⟨_, rfl⟩⟩,
        ⟨i, ⟨((proj 𝒜 i x)^m), set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 at hx,
    change ¬ ∀ (i : ℕ), (⟨mk ((proj 𝒜 i y)^m) ⟨f^i, ⟨_, rfl⟩⟩,
      ⟨i, ⟨((graded_algebra.proj 𝒜 i y)^m), set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 at hy,
    rw not_forall at hx hy,
    obtain ⟨ix, hix⟩ := hx,
    obtain ⟨iy, hiy⟩ := hy,
    intro rid,
    change ∀ (i : ℕ), (⟨mk ((proj 𝒜 i (x*y))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      ⟨i, ⟨((proj 𝒜 i (x*y))^m), set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ q.1 at rid,
    specialize rid (nx + ny),
    have eqx : nx = ix,
    { by_contra rid,
      apply hix,
      convert submodule.zero_mem _,
      rw [proj_apply, decompose_of_mem_ne 𝒜 hnx rid, zero_pow hm, localization.mk_zero], },
    have eqy : ny = iy,
    { by_contra rid,
      apply hiy,
      convert submodule.zero_mem _,
      rw [proj_apply, decompose_of_mem_ne 𝒜 hny rid, zero_pow hm, localization.mk_zero], },
    rw ←eqx at hix,
    rw ←eqy at hiy,

    have eqx2 : (⟨mk ((proj 𝒜 nx) x ^ m) ⟨f ^ nx, ⟨_, rfl⟩⟩,
      ⟨nx, ⟨(proj 𝒜 nx) x ^ m, by exact set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) =
    ⟨mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, ⟨nx, ⟨_, by exact set_like.graded_monoid.pow_mem m hnx⟩, rfl⟩⟩,
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [proj_apply, decompose_of_mem_same],
      exact hnx },
    rw eqx2 at hix,

    have eqy2 : (⟨mk ((proj 𝒜 ny) y ^ m) ⟨f ^ ny, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, by exact set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) =
      (⟨mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, by exact set_like.graded_monoid.pow_mem _ hny⟩, rfl⟩⟩ : A⁰_ f_deg),
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [proj_apply, decompose_of_mem_same],
      exact hny },
    erw eqy2 at hiy,

    rw show (⟨mk ((proj 𝒜 (nx+ny)) (x*y) ^ m)
        ⟨f^(nx+ny), ⟨_, rfl⟩⟩, ⟨nx + ny, ⟨_, by exact set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) =
      ⟨mk ((x*y)^m) ⟨f^(nx+ny), ⟨_, rfl⟩⟩, ⟨nx + ny, ⟨_, set_like.graded_monoid.pow_mem _ (mul_mem hnx hny)⟩, rfl⟩⟩,
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
      apply set_like.graded_monoid.mul_mem hnx hny, } at rid,

    rw show (⟨mk ((x*y)^m) ⟨f^(nx+ny), ⟨_, rfl⟩⟩, ⟨nx + ny, ⟨_, set_like.graded_monoid.pow_mem _ (mul_mem hnx hny)⟩, rfl⟩⟩ : A⁰_ f_deg)
    = (⟨mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, ⟨nx, ⟨_, set_like.graded_monoid.pow_mem _ hnx⟩, rfl⟩⟩ : A⁰_ f_deg) *
      (⟨mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, ⟨ny, ⟨_, set_like.graded_monoid.pow_mem _ hny⟩, rfl⟩⟩ : A⁰_ f_deg),
    { rw [subtype.ext_iff, subring.coe_mul],
      dsimp only [subtype.coe_mk],
      rw [localization.mk_mul],
      congr',
      rw mul_pow,
      rw pow_add, } at rid,

    rcases ideal.is_prime.mem_or_mem (q.is_prime) rid with L | R,
    { apply hix, exact L },
    { apply hiy, exact R }, },
end

variable (f_deg)
def to_fun (hm : 0 < m) :
  (Spec.T (A⁰_ f_deg)) → (Proj.T| (pbo f)) := λ q,
⟨⟨carrier.as_homogeneous_ideal hm q,
  carrier.as_ideal.prime hm q,
  carrier.relevant hm q⟩, begin
    erw projective_spectrum.mem_basic_open,
    intro rid,
    change ∀ i : ℕ, _ ∈ q.1 at rid,
    specialize rid m,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    convert rid,
    symmetry,
    rw [subtype.ext_iff, subring.coe_one],
    dsimp only [subtype.coe_mk],
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg],
    convert localization.mk_self _,
    refl,
  end⟩

end from_Spec

section to_Spec_from_Spec

lemma to_Spec_from_Spec {f : A} {m : ℕ}
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x : Spec.T (A⁰_ f_deg)) :
  to_Spec.to_fun 𝒜 f_deg (from_Spec.to_fun f_deg hm x) = x :=
begin
ext z, split,
{ intros hz,
  change z ∈ (to_Spec.to_fun _ f_deg (⟨⟨⟨from_Spec.carrier.as_ideal hm x, _⟩, _, _⟩, _⟩)).1 at hz,
  unfold to_Spec.to_fun at hz,
  dsimp only at hz,
  erw to_Spec.carrier_eq_carrier' at hz,
  unfold to_Spec.carrier' at hz,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
  obtain ⟨c, eq1⟩ := hz,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  erw ←eq1,
  apply ideal.sum_mem,
  rintros ⟨⟨j, j_degree_zero⟩, j_mem⟩ hj,
  change ∃ _, _ at j_mem,
  obtain ⟨s, hs, n, s_mem, eq3⟩ := j_mem,
  apply ideal.mul_mem_left,
  erw [←subtype.val_eq_coe],
  dsimp only,
  erw eq3,
  dsimp only at hs,
  change ∀ _, _ at hs,
  specialize hs (m * n),
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 s_mem] at hs,
  have eq4 : ((⟨localization.mk s ⟨f ^ n, ⟨_, rfl⟩⟩, ⟨n, ⟨s, s_mem⟩, rfl⟩⟩ : A⁰_ f_deg))^m =
    ⟨localization.mk (s^m) ⟨f^(m*n), ⟨_, rfl⟩⟩, ⟨m*n, ⟨s^m, set_like.graded_monoid.pow_mem _ s_mem⟩, rfl⟩⟩,
  { rw [subtype.ext_iff, subring.coe_pow],
    dsimp only [subtype.coe_mk],
    simp only [localization.mk_pow, mul_comm m n, pow_mul],
    refl, },
  erw ←eq4 at hs,
  exact ideal.is_prime.mem_of_pow_mem (x.is_prime) _ hs,
   },
  { intros hz,
    unfold to_Spec.to_fun,
    erw to_Spec.mem_carrier_iff,
    rcases z with ⟨z, z_degree_zero⟩,
    induction z using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨k, rfl⟩⟩⟩,
    dsimp only [subtype.coe_mk] at hz ⊢,
    change ∃ (n : ℕ), _ at z_degree_zero,
    obtain ⟨n, ⟨α, α_mem⟩, hα⟩ := z_degree_zero,
    dsimp only at hα,
    have α_mem_x : (⟨mk α ⟨f ^ n, _⟩, ⟨n, ⟨α, α_mem⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ x.1,
    { convert hz using 1,
      symmetry,
      rw subtype.ext_iff_val,
      dsimp only,
      exact hα, },
    erw hα,
    have mem1 : α ∈ from_Spec.carrier x,
    { intros j,
      by_cases ineq1 : j = m * n,
      { simp only [ineq1, graded_algebra.proj_apply],
        dsimp only,
        simp only [direct_sum.decompose_of_mem_same 𝒜 α_mem],
        have mem2 := (ideal.is_prime.pow_mem_iff_mem x.is_prime m hm).mpr α_mem_x,
        convert mem2 using 1,
        rw [subtype.ext_iff, subring.coe_pow],
        dsimp only [subtype.coe_mk],
        symmetry,
        simp only [mk_pow, mul_comm m n, pow_mul],
        refl, },
    { simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 α_mem (ne.symm ineq1), zero_pow hm, mk_zero],
      exact submodule.zero_mem _, }, },
    have eq2 : (mk α ⟨f^n, ⟨_, rfl⟩⟩ : away f) =
      mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * mk α 1,
      { rw [mk_mul, one_mul, mul_one], },
        erw eq2,
        convert ideal.mul_mem_left _ _ _,
        apply ideal.subset_span,
        refine ⟨α, mem1, rfl⟩, },
end

end to_Spec_from_Spec

section from_Spec_to_Spec

lemma from_Spec_to_Spec {f : A} {m : ℕ}
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x) :
  from_Spec.to_fun f_deg hm
    (to_Spec.to_fun 𝒜 f_deg x) = x :=
begin
  classical,
  ext z, split; intros hz,
  { change ∀ i, _ at hz,
    erw ←direct_sum.sum_support_decompose 𝒜 z,
    apply ideal.sum_mem,
    intros i hi,
    specialize hz i,
    erw to_Spec.mem_carrier_iff at hz,
    dsimp only at hz,
    rw ←graded_algebra.proj_apply,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    dsimp only [subtype.coe_mk] at eq1,
    obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq2 := calc (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
                  = (localization.mk (f^(i + N)) 1) * ∑ i in c.support, c i • i.1 : by erw eq1
              ... = (localization.mk (f^(i + N)) 1) * ∑ i in c.support.attach, c i.1 • i.1.1
                  : begin
                    congr' 1,
                    symmetry,
                    convert finset.sum_attach,
                    refl,
                  end
              ... = localization.mk (f^i) 1 * ((localization.mk (f^N) 1) * ∑ i in c.support.attach, c i.1 • i.1.1)
                  : begin
                    rw [←mul_assoc, localization.mk_mul, mul_one, pow_add],
                  end
              ... = localization.mk (f^i) 1 * (localization.mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : rfl
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
                  : by rw finset.mul_sum
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    rw finset.sum_congr rfl (λ j hj, _),
                    have := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
                    dsimp only at this,
                      erw [this, mul_comm],
                    end
              ... = localization.mk (f^i) 1 * localization.mk (∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    induction c.support.attach using finset.induction_on with a s ha ih,
                    { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
                    { erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm], },
                  end
              ... = localization.mk (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    rw [localization.mk_mul, one_mul],
                  end,
    have eq3 := calc
                (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
              = (localization.mk (f^N) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, localization.mk_mul, one_mul, one_mul, localization.mk_eq_mk', is_localization.eq],
                refine ⟨1, _⟩,
                erw [mul_one, mul_one, mul_one, pow_add, ←subtype.val_eq_coe],
                dsimp only,
                ring,
              end
          ... = (localization.mk (f^N * (graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, one_mul],
              end,
    have eq4 : ∃ (C : submonoid.powers f),
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 =
      (f^N * (graded_algebra.proj 𝒜 i z)^m) * C.1,
    { rw [eq2] at eq3,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
      obtain ⟨C, hC⟩ := eq3,
      erw [mul_one, mul_one] at hC,
      refine ⟨C, hC⟩, },
    obtain ⟨C, hC⟩ := eq4,
    have mem1 :
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 ∈ x.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.mul_mem_left,
      apply ideal.sum_mem,
      rintros ⟨j, hj⟩ _,
      have eq5 := (hacd (c j * j.1) (prop1 j hj)).2,
      dsimp only at eq5 ⊢,
      have mem2 := j.2,
      change ∃ g, _ at mem2,
      obtain ⟨g, hg1, hg2⟩ := mem2,
      have eq6 : ∃ (k : ℕ) (z : A), c j = localization.mk z ⟨f^k, ⟨_, rfl⟩⟩,
      { induction (c j) using localization.induction_on with data,
        obtain ⟨z, ⟨_, k, rfl⟩⟩ := data,
        refine ⟨_, _, rfl⟩,},
      obtain ⟨k, z, eq6⟩ := eq6,
      change localization.mk g 1 = _ at hg2,
      have eq7 := calc localization.mk (after_clear_denominator (c j * j.1) (prop1 j hj)) 1
                = c j * j.1 * localization.mk (f^N) 1 : eq5
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * j.1 * localization.mk (f^N) 1 : by rw eq6
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1 : by rw hg2
            ... = localization.mk (z*g*f^N) ⟨f^k, ⟨_, rfl⟩⟩
                : begin
                  rw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
                end,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq7,
      obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq7⟩ := eq7,
      erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq7,
      dsimp only at eq7,
      have mem3 : z * g * f ^ N * f ^ l ∈ x.1.as_homogeneous_ideal,
      { apply ideal.mul_mem_right,
        apply ideal.mul_mem_right,
        apply ideal.mul_mem_left,
        exact hg1, },
      erw [←eq7, mul_assoc, ←pow_add] at mem3,
      rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem3 with H | RID,
      { exact H, },
      { exfalso,
        have mem4 := x.2,
        erw projective_spectrum.mem_basic_open at mem4,
        apply mem4,
        replace RID := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID,
        exact RID,
        } },

    erw hC at mem1,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem1 with S | RID2,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) S with RID1 | H,
    { exfalso,
      replace RID1 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID1,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      apply RID1, },
    { replace H := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ H,
      exact H, },
    { exfalso,
      rcases C with ⟨_, ⟨k, rfl⟩⟩,
      replace RID2 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID2,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      exact RID2, }, },
  { erw from_Spec.mem_carrier_iff,
    intros i,
    dsimp only,
    have mem2 := x.1.as_homogeneous_ideal.2 i hz,
    rw ←graded_algebra.proj_apply at mem2,
    have eq1 : (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
          = localization.mk 1 ⟨f^i, ⟨_, rfl⟩⟩ * localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1,
    { erw [localization.mk_mul, one_mul, mul_one] },
    erw [to_Spec.mem_carrier_iff],
    simp only [eq1],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨(graded_algebra.proj 𝒜 i z)^m, _, rfl⟩,
    erw ideal.is_prime.pow_mem_iff_mem (x.1.is_prime),
    exact mem2,
    exact hm, },
end

lemma to_Spec.to_fun_inj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.injective (to_Spec.to_fun 𝒜 f_deg) := λ x1 x2 hx12,
begin
  convert congr_arg (from_Spec.to_fun f_deg hm) hx12; symmetry;
  apply from_Spec_to_Spec,
end

lemma to_Spec.to_fun_surj {f : A} {m : ℕ}
  (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : function.surjective (to_Spec.to_fun 𝒜 f_deg) :=
begin
  erw function.surjective_iff_has_right_inverse,
  refine ⟨from_Spec.to_fun f_deg hm, λ x, _⟩,
  rw to_Spec_from_Spec,
end

end from_Spec_to_Spec

section

variables {𝒜}

def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Spec.T (A⁰_ f_deg)) ⟶ (Proj.T| (pbo f)) :=
{ to_fun := from_Spec.to_fun f_deg hm,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact @is_topological_basis.inducing (Proj.T| (pbo f)) _ Proj _ (λ x, x.1) _ ⟨rfl⟩ (projective_spectrum.is_topological_basis_basic_opens 𝒜),

    intros s hs,
    erw set.mem_preimage at hs,
    obtain ⟨t, ht1, ht2⟩ := hs,
    rw set.mem_range at ht1,
    obtain ⟨a, rfl⟩ := ht1,
    dsimp only at ht2,
    have set_eq1 : s =
      {x | x.1 ∈ (pbo f) ⊓ (pbo a) },
    { ext x, split; intros hx,
      erw [←ht2, set.mem_preimage] at hx,
      refine ⟨x.2, hx⟩,

      rcases hx with ⟨hx1, hx2⟩,
      erw [←ht2, set.mem_preimage],
      exact hx2, },

    -- we want to use preimage = forward s,
    set set1 := to_Spec.to_fun 𝒜 f_deg '' s with set1_eq,
    have o1 : is_open set1,
    {
      suffices : is_open (to_Spec.to_fun 𝒜 f_deg '' {x | x.1 ∈ (pbo f).1 ⊓ (pbo a).1}),
      erw [set1_eq, set_eq1], exact this,

      have set_eq2 := calc to_Spec.to_fun 𝒜 f_deg ''
            {x | x.1 ∈ (pbo f) ⊓ (pbo a)}
          = to_Spec.to_fun 𝒜 f_deg ''
            {x | x.1 ∈ (pbo f) ⊓ (⨆ (i : ℕ), (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            erw projective_spectrum.basic_open_eq_union_of_projection 𝒜 a,
          end
      ... = to_Spec.to_fun 𝒜 f_deg '' 
            {x | x.1 ∈
              (⨆ (i : ℕ), (pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)) : opens Proj.T)}
          : begin
            congr',
            ext x,
            split; intros hx,
            { rcases hx with ⟨hx1, hx2⟩,
              erw opens.mem_Sup at hx2 ⊢,
              obtain ⟨_, ⟨j, rfl⟩, hx2⟩ := hx2,
              refine ⟨(pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 j a)), ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩, },
            { erw opens.mem_Sup at hx,
              obtain ⟨_, ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩ := hx,
              refine ⟨hx1, _⟩,
              erw opens.mem_Sup,
              refine ⟨pbo (graded_algebra.proj 𝒜 j a), ⟨j, rfl⟩, hx2⟩, },
          end
      ... = to_Spec.to_fun 𝒜 f_deg '' ⋃ (i : ℕ), {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            split; intros hx; dsimp only at hx ⊢,
            { change ∃ _, _ at hx,
              obtain ⟨s, hs1, hs2⟩ := hx,
              erw set.mem_image at hs1,
              obtain ⟨s, hs1, rfl⟩ := hs1,
              erw set.mem_range at hs1,
              obtain ⟨i, rfl⟩ := hs1,
              change ∃ _, _,
              refine ⟨_, ⟨i, rfl⟩, _⟩,
              exact hs2, },
            { change ∃ _, _ at hx,
              obtain ⟨_, ⟨j, rfl⟩, hx⟩ := hx,
              change x.val ∈ _ at hx,
              simp only [opens.mem_supr],
              refine ⟨j, hx⟩, },
          end
      ... = ⋃ (i : ℕ), to_Spec.to_fun 𝒜 f_deg ''
              {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
          : begin
            erw set.image_Union,
          end,
      

    erw set_eq2,
    apply is_open_Union,
    intros i,
    suffices : to_Spec.to_fun 𝒜 f_deg '' {x | x.1 ∈ ((pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a)))}
        = (sbo (⟨mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, ⟨(graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)).1,
    { erw this,
      exact (prime_spectrum.basic_open _).2 },

    suffices : to_Spec.to_fun 𝒜 f_deg ⁻¹' (sbo (⟨mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, ⟨(graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg)).1 =
      {x | x.1 ∈ (pbo f) ⊓ (pbo (graded_algebra.proj 𝒜 i a))},
    { erw ←this,
      apply function.surjective.image_preimage,
      exact to_Spec.to_fun_surj 𝒜 hm f_deg, },

    { erw to_Spec.preimage_eq f_deg ((graded_algebra.proj 𝒜 i a)^m) i,
      erw projective_spectrum.basic_open_pow,
      exact hm } },

    suffices : set1 = from_Spec.to_fun f_deg hm ⁻¹' _,
    erw ←this,
    exact o1,

    { erw set1_eq,
      ext z, split; intros hz,
      { erw set.mem_preimage,
        erw set.mem_image at hz,
        obtain ⟨α, α_mem, rfl⟩ := hz,
        erw from_Spec_to_Spec,
        exact α_mem, },
      { erw set.mem_preimage at hz,
        erw set.mem_image,
        refine ⟨from_Spec.to_fun f_deg hm z, hz, _⟩,
        erw to_Spec_from_Spec, }, },
  end }

end

end Proj_iso_Spec_Top_component

section

variables {𝒜}
def Proj_iso_Spec_Top_component {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f_deg)) :=
{ hom := Proj_iso_Spec_Top_component.to_Spec m f_deg,
  inv := Proj_iso_Spec_Top_component.from_Spec hm f_deg,
  hom_inv_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply Proj_iso_Spec_Top_component.from_Spec_to_Spec,
  end,
  inv_hom_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  end }

end

end algebraic_geometry