import ring_theory.localization.basic
import algebraic_geometry.structure_sheaf

import cicm2022.internal.graded_ring

section

open_locale big_operators

variables {R : Type*} [comm_ring R] (M : submonoid R)

lemma localization.mk_sum {ι : Type*} (m : M) (s : finset ι) (f : ι → R) :
  localization.mk (∑ i in s, f i) m = ∑ i in s, localization.mk (f i) m :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  induction s using finset.induction_on with i s hi ih,
  { simp },
  { rw [finset.sum_insert hi, finset.sum_insert hi, ← ih, localization.add_mk],
    simp only [localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [submonoid.coe_one, submonoid.coe_mul, mul_one],
    ring, }
end

end

section

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜]

lemma graded_algebra.proj_hom_mul (a b : A) (i j : ℕ) (a_mem : a ∈ 𝒜 i)
  (hb : graded_algebra.proj 𝒜 j b ≠ 0) :
  graded_algebra.proj 𝒜 (i + j) (a * b) = a * graded_algebra.proj 𝒜 j b :=
begin
  classical,
  by_cases INEQ : a = 0,
  rw [INEQ, zero_mul, zero_mul, linear_map.map_zero],

  rw [graded_algebra.proj_apply, show direct_sum.decompose 𝒜 (a * b) (i + j) = direct_sum.decompose_alg_equiv _ _ _, from rfl,
    alg_equiv.map_mul, direct_sum.coe_mul_apply],

  have set_eq1 : (direct_sum.decompose_alg_equiv 𝒜 a).support = {i},
    { ext1, split; intros hx,
      { erw graded_algebra.mem_support_iff at hx,
        erw finset.mem_singleton,
        contrapose hx,
        erw [not_not, graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne],
        exact a_mem,
        symmetry,
        exact hx, },
      { rw finset.mem_singleton at hx,
        rw [hx, dfinsupp.mem_support_iff, show direct_sum.decompose_alg_equiv 𝒜 a i = direct_sum.decompose 𝒜 a i, from rfl],
        intros r,
        have := direct_sum.decompose_of_mem_same 𝒜 a_mem,
        rw r at this,
        apply INEQ,
        rw ←this,
        refl, }, },
    rw [set_eq1],
    have set_eq2 : finset.filter
          (λ z : ℕ × ℕ, z.1 + z.2 = i + j)
          (finset.product
            {i}
            ((direct_sum.decompose_alg_equiv 𝒜 b).support)) =
      {(i, j)},
    { ext1 x, rcases x with ⟨n1, n2⟩,
      split; intros ha,
      { erw finset.mem_filter at ha,
        rcases ha with ⟨ha1, ha3⟩,
        erw finset.mem_product at ha1,
        rcases ha1 with ⟨ha1, ha2⟩,
        dsimp only at ha1 ha2 ha3,
        erw finset.mem_singleton at ha1,
        erw finset.mem_singleton,
        ext; dsimp only,
        { exact ha1, },
        { erw ha1 at ha3,
          linarith, }, },
      { erw [finset.mem_singleton, prod.ext_iff] at ha,
        rcases ha with ⟨ha1, ha2⟩,
        dsimp only at ha1 ha2,
        erw [ha1, ha2, finset.mem_filter, finset.mem_product, finset.mem_singleton],
        refine ⟨⟨rfl, _⟩, rfl⟩,
        dsimp only,
        erw graded_algebra.mem_support_iff,
        exact hb, }, },
    rw [set_eq2, finset.sum_singleton],
    dsimp only,
    erw [direct_sum.decompose_of_mem_same 𝒜, ←graded_algebra.proj_apply],
    exact a_mem,
end

end

namespace algebraic_geometry.structure_sheaf

open topological_space algebraic_geometry opposite

variables (R : Type*) [comm_ring R]

lemma is_locally_fraction_pred'
  {U : opens (prime_spectrum.Top R)} (f : Π x : U, localizations R x) :
  (is_locally_fraction R).pred f ↔
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V, ∃ (s_not_mem : ¬ (s ∈ y.1.as_ideal)),
    f (i y : U) = localization.mk r ⟨s, s_not_mem⟩ :=
begin
  rw is_locally_fraction_pred,
  split; intros H,
  { rintros x,
    obtain ⟨V, m, i, r, s, H⟩ := H x,
    refine ⟨V, m, i, r, s, _⟩,
    intros y,
    obtain ⟨s_not_mem, H⟩ := H y,
    refine ⟨s_not_mem, _⟩,
    rw [localization.mk_eq_mk'],
    erw is_localization.eq_mk'_iff_mul_eq,
    exact H, },
  { intros x,
    obtain ⟨V, m, i, r, s, H⟩ := H x,
    refine ⟨V, m, i, r, s, _⟩,
    intros y,
    obtain ⟨s_not_mem, H⟩ := H y,
    refine ⟨s_not_mem, _⟩,
    rw [localization.mk_eq_mk'] at H,
    erw is_localization.eq_mk'_iff_mul_eq at H,
    exact H },
end

lemma one_val (U : opens (prime_spectrum.Top R)) :
  (1 : sections_subring R (op U)).1 = 1 := rfl

lemma zero_val (U : opens (prime_spectrum.Top R)) :
  (0 : sections_subring R (op U)).1 = 0 := rfl

lemma add_val (U : opens (prime_spectrum.Top R)) (x y : sections_subring R (op U)) :
  (x + y : sections_subring R (op U)).1 = x.1 + y.1 := rfl

lemma mul_val (U : opens (prime_spectrum.Top R)) (x y : sections_subring R (op U)) :
  (x * y : sections_subring R (op U)).1 = x.1 * y.1 := rfl


end algebraic_geometry.structure_sheaf


section clear_denominator

variables {A : Type*} [comm_ring A]

open localization

-- this is a wrapper around `is_localization.exist_integer_multiples_of_finset`, the main purpose
-- of this lemma is to make the degree of denominator explicit.
lemma clear_denominator {f : A} (s : finset (away f)) :
  ∃ (n : ℕ), ∀ (x : away f), x ∈ s →
    x * (mk (f^n) 1 : away f) ∈
    (λ y, (mk y 1 : localization.away f)) '' set.univ :=
begin
  rcases is_localization.exist_integer_multiples_of_finset (submonoid.powers f) s with
    ⟨⟨_, ⟨n, rfl⟩⟩, h⟩,
  refine ⟨n, λ x hx, _⟩,
  rcases h x hx with ⟨a, eq1⟩,
  induction x using localization.induction_on with data,
  rcases data with ⟨x, y⟩,
  dsimp at *,
  change mk a 1 = f^n • _ at eq1,
  rw [algebra.smul_def, show algebra_map A (localization.away f) _ = mk (f^_) 1, from rfl, mk_mul, one_mul] at eq1,
  rw [mk_mul, mul_one, mul_comm, ← eq1],
  refine ⟨a, trivial, rfl⟩,
end

end clear_denominator
