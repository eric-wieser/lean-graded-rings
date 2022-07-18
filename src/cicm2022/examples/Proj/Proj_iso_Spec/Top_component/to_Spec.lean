import cicm2022.examples.Proj.degree_zero_part
import cicm2022.examples.Proj.structure_sheaf
import cicm2022.examples.Proj.lemmas

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

namespace to_Spec

open ideal

variables {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| (pbo f))

/--For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : ideal (A⁰_ f_deg) :=
ideal.comap (algebra_map (A⁰_ f_deg) (away f))
  (ideal.span $ algebra_map A (away f) '' x.1.as_homogeneous_ideal)

lemma mem_carrier_iff (z : A⁰_ f_deg) :
  z ∈ carrier f_deg x ↔
  ↑z ∈ ideal.span (algebra_map A (away f) '' x.1.as_homogeneous_ideal) :=
iff.rfl

lemma mem_carrier.clear_denominator [decidable_eq (away f)]
  {z : A⁰_ f_deg} (hz : z ∈ carrier f_deg x) :
  ∃ (c : algebra_map A (away f) '' x.1.as_homogeneous_ideal →₀ away f)
    (N : ℕ)
    (acd : Π y ∈ c.support.image c, A),
    f ^ N • ↑z =
    algebra_map A (away f) (∑ i in c.support.attach,
      acd (c i) (finset.mem_image.mpr ⟨i, ⟨i.2, rfl⟩⟩) * classical.some i.1.2) :=
begin
  rw [mem_carrier_iff, ←submodule_span_eq, finsupp.span_eq_range_total, linear_map.mem_range] at hz,
  rcases hz with ⟨c, eq1⟩,
  rw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := is_localization.exist_integer_multiples_of_finset (submonoid.powers f)
    (c.support.image c),
  choose acd hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },

  refine ⟨c, N, acd, _⟩,
  rw [← eq1, smul_sum, map_sum, ← sum_attach],
  congr' 1,
  ext i,
  rw [_root_.map_mul, hacd, (classical.some_spec i.1.2).2, smul_eq_mul, smul_mul_assoc],
  refl
end

def carrier' : ideal (A⁰_ f_deg) :=
ideal.span
  { z | ∃ (s : A) (hs : s ∈ x.1.as_homogeneous_ideal) (n : ℕ) (s_mem : s ∈ 𝒜 (m * n)), 
      z = ⟨mk s ⟨f^n, ⟨_, rfl⟩⟩, ⟨n, ⟨s, s_mem⟩, rfl⟩⟩ }

lemma carrier_eq_carrier' :
  carrier f_deg x = carrier' f_deg x :=
begin
  classical,
  -- haveI : decidable_eq (away f) := classical.dec_eq _,
  ext z, split; intros hz,
  { rw mem_carrier_iff at hz,
    change z ∈ ideal.span _,
    have mem1 := z.prop,
    change ∃ _, _ at mem1,
    obtain ⟨k, ⟨a, a_mem⟩, hk⟩ := mem1,
    erw [hk] at hz,

    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    dsimp only [subtype.coe_mk] at eq1,

    suffices mem1 : a ∈ x.1.as_homogeneous_ideal,
    apply ideal.subset_span,
    exact ⟨a, mem1, _, a_mem, subtype.ext hk⟩,

    obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i ∈ (finset.image (λ i, c i * i) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq3 := calc (localization.mk a 1 : localization.away f) * localization.mk (f^N) 1
            = localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^k) 1 * localization.mk (f^N) 1
            : begin
              congr,
              rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
              use 1,
              erw [mul_one, mul_one, mul_one, mul_one, subtype.coe_mk],
            end
        ... = localization.mk (f^k) 1 * localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
            : by ring
        ... = localization.mk (f^k) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i
            : begin
              erw eq1, ring,
            end
        ... = localization.mk (f^k) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i) : by ring
        ... = localization.mk (f^k) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i)
            : begin
              congr' 1,
              rw finset.mul_sum,
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i * i.1.1)
            : begin
              congr' 1,
              symmetry,
              convert finset.sum_attach,
              refl,
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i * i.1.1) (prop1 i i.prop)) 1)
            : begin
              congr' 1,
              rw finset.sum_congr rfl (λ j hj, _),
              have eq2 := (hacd (c j * j.1.1) (prop1 j.1 j.2)).2,
              dsimp only at eq2,
              erw eq2,
              rw mul_comm,
            end
        ... = ∑ i in c.support.attach, (localization.mk (f^k) 1) * (localization.mk (after_clear_denominator (c i * i.1.1) (prop1 i i.prop)) 1)
            : begin
              rw finset.mul_sum,
            end
        ... = ∑ i in c.support.attach, localization.mk (f^k * (after_clear_denominator (c i * i.1.1) (prop1 i i.prop))) 1
            : begin
              rw finset.sum_congr rfl (λ j hj, _),
              erw [localization.mk_mul, one_mul],
            end
        ... = localization.mk (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i * i.1.1) (prop1 i i.prop)))) 1
            : begin
              induction c.support.attach using finset.induction_on with y s hy ih,
              rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],

              erw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm],
            end,
    erw [localization.mk_mul, one_mul] at eq3,
    simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
    obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
    erw [mul_one, mul_one] at eq3,
    dsimp only [subtype.coe_mk] at eq3,

    suffices : (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i * i.1.1) (prop1 i i.prop)))) * f^l ∈ x.1.as_homogeneous_ideal,
    erw ←eq3 at this,
    rcases x.1.is_prime.mem_or_mem this with H1 | H3,
    rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact H1 },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H2,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H3,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },

    apply ideal.mul_mem_right,
    apply ideal.sum_mem,
    intros j hj,
    apply ideal.mul_mem_left,
    set g := classical.some j.1.2 with g_eq,
    have mem3 : g ∈ x.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
    have eq3 := (classical.some_spec j.1.2).2,
    have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
    have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
    dsimp only at eq4,

    have eq5 : ∃ (a : A) (z : ℕ), c j.1 = localization.mk a ⟨f^z, ⟨z, rfl⟩⟩,
    { induction (c j.1) using localization.induction_on with data,
      rcases data with ⟨a, ⟨_, ⟨z, rfl⟩⟩⟩,
      refine ⟨a, z, rfl⟩, },
    obtain ⟨α, z, hz⟩ := eq5,

    have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
            = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
        ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
            : by erw hz
        ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
            : by erw eq3
        ... = localization.mk (α * g * f^N) ⟨f^z, ⟨z, rfl⟩⟩
            : begin
              erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
            end,
    simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
    obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
    erw [mul_one] at eq6,
    dsimp only at eq6,

    have mem4 : α * g * f ^ N * f ^ v ∈ x.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.mul_mem_right,
      apply ideal.mul_mem_left,
      exact mem3, },
    erw ←eq6 at mem4,

    rcases x.1.is_prime.mem_or_mem mem4 with H1 | H3,
    rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact H1 },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H2,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H3,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, } },

  { change z ∈ ideal.span _ at hz,
    rw mem_carrier_iff,

    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    erw [←eq1, add_submonoid_class.coe_finset_sum],

    apply ideal.sum_mem (ideal.span _),

    rintros j hj,
    rw [smul_eq_mul, subring.coe_mul],
    apply ideal.mul_mem_left (ideal.span _),
    have hj2 := j.prop,
    change ∃ s, _ at hj2,
    obtain ⟨s, hs, n, s_mem, hj2⟩ := hj2,
    erw hj2, dsimp only [subtype.coe_mk],
    have eq2 : (localization.mk s ⟨f ^ n, ⟨_, rfl⟩⟩ : localization.away f) =
      localization.mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * localization.mk s 1,
    { rw [localization.mk_mul, one_mul, mul_one], },
    erw eq2,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨s, hs, rfl⟩, },
end

lemma no_intersection :
  (x.1.as_homogeneous_ideal.to_ideal ∩ submonoid.powers f : set A) = ∅ :=
begin
  by_contra rid,
  rw [←ne.def, set.ne_empty_iff_nonempty] at rid,
  choose g hg using rid,
  obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg,
  by_cases k_ineq : 0 < k,
  { erw x.1.is_prime.pow_mem_iff_mem _ k_ineq at hg1,
    exact x.2 hg1 },
  { erw [show k = 0, by linarith, pow_zero, ←ideal.eq_top_iff_one] at hg1,
    apply x.1.is_prime.1,
    exact hg1 },
end

lemma carrier_ne_top :
  carrier f_deg x ≠ ⊤ :=
begin
  have eq_top := no_intersection x,
  classical,
  contrapose! eq_top,
  obtain ⟨c, N, acd, eq1⟩ := mem_carrier.clear_denominator _ x ((ideal.eq_top_iff_one _).mp eq_top),
  rw [algebra.smul_def, subring.coe_one, mul_one] at eq1,
  change localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  erw [mul_one, mul_one] at eq1,
  refine set.ne_empty_iff_nonempty.mpr ⟨f^N * f^M, eq1.symm ▸ mul_mem_right _ _
    (sum_mem _ (λ i hi, mul_mem_left _ _ _)), ⟨N+M, by rw pow_add⟩⟩,
  generalize_proofs h,
  exact (classical.some_spec h).1,
end

/--The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `Top_component.forward`.
-/
def to_fun : (Proj.T| (pbo f)) → (Spec.T (A⁰_ f_deg)) := λ x,
⟨carrier f_deg x, carrier_ne_top f_deg x, λ x1 x2 hx12, begin
  haveI : decidable_eq (away f) := classical.dec_eq _,
  rcases ⟨x1, x2⟩ with ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩,
  induction x1 using localization.induction_on with data_x1,
  induction x2 using localization.induction_on with data_x2,
  rcases ⟨data_x1, data_x2⟩ with ⟨⟨a1, _, ⟨n1, rfl⟩⟩, ⟨a2, _, ⟨n2, rfl⟩⟩⟩,
  rcases mem_carrier.clear_denominator f_deg x hx12 with ⟨c, N, acd, eq1⟩,
  simp only [subring.coe_mul, localization.mk_mul, mul_one, algebra.smul_def, subtype.coe_mk] at eq1,
  change localization.mk (f ^ N) 1 * mk _ (⟨f ^ n1 * f ^ n2, _⟩) = mk (∑ _, _) _ at eq1,
  rw [mk_mul, one_mul] at eq1,
  simp only [mk_mul, mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  rw [submonoid.coe_one, mul_one] at eq1,
  simp only [← subtype.val_eq_coe, submonoid.coe_mul] at eq1,

  rcases x.1.is_prime.mem_or_mem (show a1 * a2 * f ^ N * f ^ M ∈ _, from _) with h1|rid2,
  rcases x.1.is_prime.mem_or_mem h1 with h1|rid1,
  rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
  { left,
    rw mem_carrier_iff,
    simp only [show (mk a1 ⟨f ^ n1, _⟩ : away f) = mk a1 1 * mk 1 ⟨f^n1, ⟨n1, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h1, rfl⟩), },
  { right,
    rw mem_carrier_iff,
    simp only [show (mk a2 ⟨f ^ n2, _⟩ : away f) = mk a2 1 * mk 1 ⟨f^n2, ⟨n2, rfl⟩⟩,
      by rw [localization.mk_mul, mul_one, one_mul]],
    exact ideal.mul_mem_right _ _ (ideal.subset_span ⟨_, h2, rfl⟩), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem N rid1)), },
  { exact false.elim (x.2 (x.1.is_prime.mem_of_pow_mem M rid2)), },
  { rw [mul_comm _ (f^N), eq1],
    refine mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
    generalize_proofs h,
    exact (classical.some_spec h).1 },
end⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in  `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
lemma preimage_eq (a : A) (n : ℕ)
  (a_mem_degree_zero : (mk a ⟨f ^ n, ⟨n, rfl⟩⟩ : away f) ∈ A⁰_ f_deg) :
  to_fun 𝒜 f_deg ⁻¹'
      (sbo (⟨mk a ⟨f ^ n, ⟨_, rfl⟩⟩, a_mem_degree_zero⟩ : A⁰_ f_deg)).1
  = {x | x.1 ∈ (pbo f) ⊓ (pbo a)} :=
begin
  haveI : decidable_eq (away f) := classical.dec_eq _,
  ext1 y, split; intros hy,
  { refine ⟨y.2, _⟩,
    rw [set.mem_preimage, subtype.val_eq_coe, opens.mem_coe, prime_spectrum.mem_basic_open] at hy,
    rw projective_spectrum.mem_coe_basic_open,
    intro a_mem_y,
    apply hy,
    rw [to_fun, mem_carrier_iff],
    simp only [show (mk a ⟨f^n, ⟨_, rfl⟩⟩ : away f) = mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * mk a 1,
      by rw [mk_mul, one_mul, mul_one]],
    exact ideal.mul_mem_left _ _ (ideal.subset_span ⟨_, a_mem_y, rfl⟩), },
  { change y.1 ∈ _ at hy,
    rcases hy with ⟨hy1, hy2⟩,
    rw projective_spectrum.mem_coe_basic_open at hy1 hy2,
    rw [set.mem_preimage, to_fun, subtype.val_eq_coe, opens.mem_coe, prime_spectrum.mem_basic_open],
    intro rid,
    rcases mem_carrier.clear_denominator f_deg _ rid with ⟨c, N, acd, eq1⟩,
    rw [algebra.smul_def] at eq1,
    change localization.mk (f^N) 1 * mk _ _ = mk (∑ _, _) _ at eq1,
    rw [mk_mul, one_mul, mk_eq_mk', is_localization.eq] at eq1,
    rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
    rw [submonoid.coe_one, mul_one] at eq1,
    simp only [subtype.coe_mk] at eq1,

    rcases y.1.is_prime.mem_or_mem (show a * f ^ N * f ^ M ∈ _, from _) with H1 | H3,
    rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact hy2 H1, },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem N H2), },
    { exact y.2 (y.1.is_prime.mem_of_pow_mem M H3), },
    { rw [mul_comm _ (f^N), eq1],
      refine mul_mem_right _ _ (mul_mem_right _ _ (sum_mem _ (λ i hi, mul_mem_left _ _ _))),
      generalize_proofs h,
      exact (classical.some_spec h).1, }, },
end

end to_Spec

section

variable {𝒜}

/--The continuous function between the basic open set `D(f)` in `Proj` to the corresponding basic
open set in `Spec A⁰_f`.
-/
def to_Spec {f : A} (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj.T| (pbo f)) ⟶ (Spec.T (A⁰_ f_deg)) :=
{ to_fun := to_Spec.to_fun 𝒜 f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous (prime_spectrum.is_topological_basis_basic_opens),
    rintros _ ⟨⟨g, hg⟩, rfl⟩,
    induction g using localization.induction_on with data,
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data,

    erw to_Spec.preimage_eq,
    refine is_open_induced_iff.mpr ⟨(pbo f).1 ⊓ (pbo a).1, is_open.inter (pbo f).2 (pbo a).2, _⟩,
    ext z, split; intros hz; simpa [set.mem_preimage],
  end }

end

end Proj_iso_Spec_Top_component

end algebraic_geometry