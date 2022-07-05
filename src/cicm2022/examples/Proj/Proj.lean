/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import ring_theory.graded_algebra.radical
import ..Proj.lemmas

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

section
variable {𝒜}
/--
The degree zero part of the localized ring `Aₓ` is the subring of elements of the form `a/x^n` such
that `a` and `x^n` have the same degree.
-/
def degree_zero_part {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) : subring (away f) :=
{ carrier := { y | ∃ (n : ℕ) (a : 𝒜 (m * n)), y = mk a.1 ⟨f^n, ⟨n, rfl⟩⟩ },
  mul_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨a.1 * b.1, (mul_add m n n').symm ▸ mul_mem a.2 b.2⟩,
    by {rw mk_mul, congr' 1, simp only [pow_add], refl }⟩⟩,
  one_mem' := ⟨0, ⟨1, (mul_zero m).symm ▸ one_mem⟩,
    by { symmetry, convert ← mk_self 1, simp only [pow_zero], refl, }⟩,
  add_mem' := λ _ _ ⟨n, ⟨a, h⟩⟩ ⟨n', ⟨b, h'⟩⟩, h.symm ▸ h'.symm ▸
    ⟨n+n', ⟨⟨f ^ n * b.1 + f ^ n' * a.1, (mul_add m n n').symm ▸
      add_mem (mul_mem (by { rw mul_comm, exact set_like.graded_monoid.pow_mem n f_deg }) b.2)
        begin
          rw add_comm,
          refine mul_mem _ a.2,
          rw mul_comm,
          exact set_like.graded_monoid.pow_mem _ f_deg
        end⟩, begin
          rw add_mk,
          congr' 1,
          simp only [pow_add],
          refl,
        end⟩⟩,
  zero_mem' := ⟨0, ⟨0, (mk_zero _).symm⟩⟩,
  neg_mem' := λ x ⟨n, ⟨a, h⟩⟩, h.symm ▸ ⟨n, ⟨-a, neg_mk _ _⟩⟩ }

end

local notation `A⁰_` f_deg := degree_zero_part f_deg

section

variable {𝒜}

instance (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) : comm_ring (A⁰_ f_deg) :=
(degree_zero_part f_deg).to_comm_ring

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks this natural number `n`
-/
def degree_zero_part.deg {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) : ℕ :=
x.2.some

/--
Every element in the degree zero part of `Aₓ` can be written as `a/x^n` for some `a` and `n : ℕ`,
`degree_zero_part.deg` picks the numerator `a`
-/
def degree_zero_part.num {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) : A :=
x.2.some_spec.some.1

lemma degree_zero_part.num_mem {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) :
  degree_zero_part.num x ∈ 𝒜 (m * degree_zero_part.deg x) :=
x.2.some_spec.some.2

lemma degree_zero_part.eq {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m} (x : A⁰_ f_deg) :
  x.1 = mk (degree_zero_part.num x) ⟨f^(degree_zero_part.deg x), ⟨_, rfl⟩⟩ :=
x.2.some_spec.some_spec

lemma degree_zero_part.mul_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x y : A⁰_ f_deg) :
  (x * y).1 = x.1 * y.1 := rfl

lemma degree_zero_part.add_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x y : A⁰_ f_deg) :
  (x + y).1 = x.1 + y.1 := rfl

lemma degree_zero_part.sum_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) {ι : Type*} (s : finset ι) (g : ι → A⁰_ f_deg) :
  (∑ i in s, g i).val = ∑ i in s, (g i).val :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  induction s using finset.induction_on with i s hi ih,
  { simp },
  { simp },
end

lemma degree_zero_part.one_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) :
  (1 : degree_zero_part f_deg).1 = 1 := rfl

lemma degree_zero_part.zero_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) :
  (0 : degree_zero_part f_deg).1 = 0 := rfl

lemma degree_zero_part.pow_val {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : A⁰_ f_deg) (n : ℕ) :
  (x ^ n).1 = x.1 ^ n :=
nat.rec_on n (by rw [pow_zero, degree_zero_part.one_val, pow_zero]) $ λ i ih, 
by rw [pow_succ, degree_zero_part.mul_val, ih, pow_succ]


end

section clear_denominator

-- this is a wrapper around `is_localization.exist_integer_multiples_of_finset`, the main purpose
-- of this lemma is to make the degree of denominator explicit.
private lemma clear_denominator {f : A} (s : finset (away f)) :
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

namespace Proj_iso_Spec_Top_component

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/

namespace to_Spec

open ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.

variables {𝒜} {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (x : Proj| (pbo f))

/--For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `Top_component.forward.to_fun`-/
def carrier : ideal (A⁰_ f_deg) :=
ideal.comap (algebra_map (A⁰_ f_deg) (away f))
  (ideal.span $ algebra_map A (away f) '' x.1.as_homogeneous_ideal)

lemma mem_carrier_iff (z : A⁰_ f_deg) :
  z ∈ carrier f_deg x ↔
  z.1 ∈ ideal.span (algebra_map A (away f) '' x.1.as_homogeneous_ideal) :=
iff.rfl

lemma mem_carrier.clear_denominator [decidable_eq (away f)]
  {z : A⁰_ f_deg} (hz : z ∈ carrier f_deg x) :
  ∃ (c : algebra_map A (away f) '' x.1.as_homogeneous_ideal →₀ away f)
    (N : ℕ)
    (acd : Π y ∈ c.support.image c, A),
    f ^ N • z.1 =
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
    have mem1 := z.2,
    change ∃ _, _ at mem1,
    obtain ⟨k, ⟨a, a_mem⟩, hk⟩ := mem1,
    erw [hk] at hz,

    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,

    suffices mem1 : a ∈ x.1.as_homogeneous_ideal,
    apply ideal.subset_span,
    refine ⟨a, mem1, _, a_mem, _⟩,
    rw subtype.ext_iff_val, dsimp only, rw hk,

    obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq3 := calc (localization.mk a 1 : localization.away f) * localization.mk (f^N) 1
            = localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^k) 1 * localization.mk (f^N) 1
            : begin
              congr,
              rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
              use 1,
              erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
            end
        ... = localization.mk (f^k) 1 * localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
            : by ring
        ... = localization.mk (f^k) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
            : begin
              erw eq1, ring,
            end
        ... = localization.mk (f^k) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
        ... = localization.mk (f^k) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
            : begin
              congr' 1,
              rw finset.mul_sum,
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
            : begin
              congr' 1,
              symmetry,
              convert finset.sum_attach,
              refl,
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
            : begin
              congr' 1,
              rw finset.sum_congr rfl (λ j hj, _),
              have eq2 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
              dsimp only at eq2,
              erw eq2,
              rw mul_comm,
            end
        ... = ∑ i in c.support.attach, (localization.mk (f^k) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
            : begin
              rw finset.mul_sum,
            end
        ... = ∑ i in c.support.attach, localization.mk (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
            : begin
              rw finset.sum_congr rfl (λ j hj, _),
              erw [localization.mk_mul, one_mul],
            end
        ... = localization.mk (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
            : begin
              induction c.support.attach using finset.induction_on with y s hy ih,
              rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],

              erw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm],
            end,
        erw [localization.mk_mul, one_mul] at eq3,
        simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
        obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
        erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
        dsimp only at eq3,

    suffices : (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ x.1.as_homogeneous_ideal,
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
    erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
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

    erw [←eq1, show (∑ i in c.support, c i * i.1).val = ∑ i in c.support, (c i).1 * i.1.1, begin
      induction c.support using finset.induction_on with a s ha ih,

      rw [finset.sum_empty, finset.sum_empty],
      refl,

      erw [finset.sum_insert ha, finset.sum_insert ha, ←ih],
      dsimp only,
      refl,
    end],

    eapply ideal.sum_mem (ideal.span _),

    rintros j hj,
    eapply ideal.mul_mem_left (ideal.span _),
    have hj2 := j.2,
    change ∃ s, _ at hj2,
    obtain ⟨s, hs, n, s_mem, hj2⟩ := hj2,
    erw hj2, dsimp only,
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
  rw [algebra.smul_def, subtype.val_eq_coe, subring.coe_one, mul_one] at eq1,
  change localization.mk (f ^ N) 1 = mk (∑ _, _) 1 at eq1,
  simp only [mk_eq_mk', is_localization.eq] at eq1,
  rcases eq1 with ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩,
  erw [mul_one, mul_one] at eq1,
  simp only [← subtype.val_eq_coe] at eq1,
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
  simp only [degree_zero_part.mul_val, localization.mk_mul, mul_one, algebra.smul_def] at eq1,
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

namespace from_Spec

-- in this section we construct a function from `Spec.T (A⁰_f)` to `Proj.T`, i.e.
-- given `q : Spec.T (A⁰_f)`, we need a point in `Proj`.
-- Equivalently, for a prime ideal `q` in `A⁰_f`, we need a relevant homogeneous prime ideal in A.

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
    { rw [subtype.ext_iff_val, degree_zero_part.mul_val, mk_mul],
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
                  { exact set_like.graded_monoid.nat_mem _ _, },
                  rw show m * (2 * i) = ((j.1*i) + (2*m-j.1)*i + 0),
                  { zify,
                    rw [show (↑(2 * m - j.1) : ℤ) = 2 * m - j.1,
                    { rw [eq_sub_iff_add_eq, ←int.coe_nat_add, nat.sub_add_cancel (nat.lt_succ_iff.mp (mem_range.mp j.2))],
                      refl, }, sub_mul, add_zero],
                    ring, },
                  apply set_like.graded_monoid.mul_mem _ mem3,
                  apply set_like.graded_monoid.mul_mem mem1 mem2,
                end⟩, rfl⟩⟩
            : by simp only [subtype.ext_iff_val, degree_zero_part.sum_val, localization.mk_sum],
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
              { exact set_like.graded_monoid.nat_mem _ _, },
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
            { apply set_like.graded_monoid.nat_mem, },
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
                rw [subtype.ext_iff_val, degree_zero_part.mul_val],
                dsimp only,
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
    rw [subtype.ext_iff_val, degree_zero_part.one_val],
    dsimp only,
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
    rw [subtype.ext_iff_val, degree_zero_part.one_val],
    dsimp only,
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
    { rw [subtype.ext_iff_val, degree_zero_part.mul_val],
      dsimp only,
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
    rw [subtype.ext_iff_val, degree_zero_part.one_val],
    dsimp only,
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
  { rw [subtype.ext_iff_val, degree_zero_part.pow_val],
    dsimp only,
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
    dsimp only at hz ⊢,
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
        rw [subtype.ext_iff_val, degree_zero_part.pow_val],
        dsimp only,
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

namespace Proj_iso_Spec_Sheaf_component

namespace to_Spec

variables {𝒜} {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
variable (U : (opens (Spec.T (A⁰_ f_deg)))ᵒᵖ)

local notation `pf_sheaf` x := (Proj_iso_Spec_Top_component hm f_deg).hom _* x.presheaf -- pushforward a sheaf

variable (hh : (pf_sheaf (Proj| (pbo f))).obj U)

lemma pf_sheaf.one_val :
  (1 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 1 := rfl

lemma pf_sheaf.zero_val :
  (0 : (pf_sheaf (Proj| (pbo f))).obj U).1 = 0 := rfl

lemma pf_sheaf.add_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x + y).1 = x.1 + y.1 := rfl

lemma pf_sheaf.mul_val (x y : (pf_sheaf (Proj| (pbo f))).obj U) :
  (x * y).1 = x.1 * y.1 := rfl

variables {f_deg hm U}
lemma inv_mem (y : unop U) :
  ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj 
      ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  refine ⟨⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).2⟩, _, rfl⟩,
  change _ ∈ _ ⁻¹' _,
  erw set.mem_preimage,
  change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm y.1)) ∈ _,
  erw Proj_iso_Spec_Top_component.to_Spec_from_Spec 𝒜 hm f_deg y.1,
  exact y.2,
end

variable (hm)
def hl (y : unop U) : homogeneous_localization 𝒜 _ :=
hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩

lemma hl.one (y : unop U) :
  hl hm 1 y = 1 :=
by rw [hl, pf_sheaf.one_val, pi.one_apply]

lemma hl.zero (y : unop U) :
  hl hm 0 y = 0 :=
by rw [hl, pf_sheaf.zero_val, pi.zero_apply]

lemma hl.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm (x + y) z = hl hm x z + hl hm y z :=
by rw [hl, pf_sheaf.add_val, pi.add_apply, hl, hl]

lemma hl.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  hl hm (x * y) z = hl hm x z * hl hm y z :=
by rw [hl, hl, hl, pf_sheaf.mul_val, pi.mul_apply]


def num (y : unop U) : A⁰_ f_deg :=
⟨mk ((hl hm hh y).num * (hl hm hh y).denom ^ m.pred) ⟨f^(hl hm hh y).deg, ⟨_, rfl⟩⟩, 
  ⟨(hl hm hh y).deg, ⟨(hl hm hh y).num * (hl hm hh y).denom ^ m.pred, begin
    convert mul_mem (hl hm hh y).num_mem (set_like.graded_monoid.pow_mem m.pred (hl hm hh y).denom_mem), 
    exact calc m * (hl hm hh y).deg
            = (m.pred + 1) * (hl hm hh y).deg
            : begin
              congr,
              conv_lhs { rw ←nat.succ_pred_eq_of_pos hm },
            end
        ... = m.pred * (hl hm hh y).deg +
              1 * (hl hm hh y).deg
            : by rw add_mul
        ... = _ : begin
          rw [add_comm, one_mul],
          congr,
        end,
  end⟩, rfl⟩⟩

def denom (y : unop U) : A⁰_ f_deg :=
⟨mk ((hl hm hh y).denom ^ m) ⟨f^(hl hm hh y).deg, ⟨_, rfl⟩⟩, 
  ⟨(hl hm hh y).deg, ⟨_, set_like.graded_monoid.pow_mem m (hl hm hh y).denom_mem⟩, rfl⟩⟩

lemma denom.not_mem (y : unop U) : denom hm hh y ∉ y.1.as_ideal := λ r,
begin
  have prop1 := (hl hm hh y).denom_not_mem,
  change _ ∉ (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm y.1).1.as_homogeneous_ideal at prop1,
  contrapose! prop1,
  change ∀ _, _,

  contrapose! prop1,
  obtain ⟨n, hn⟩ := prop1,

  have eq1 : (hl hm hh y).deg = n,
  { -- n ≠ i, contradiction,
    by_contra ineq,
    simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne 𝒜 ((hl hm hh y).denom_mem) ineq, zero_pow hm, mk_zero] at hn,
    apply hn,
    exact submodule.zero_mem _, },
  apply hn,
  convert r,

  rw [graded_algebra.proj_apply, ←eq1, direct_sum.decompose_of_mem_same],
  exact (hl hm hh y).denom_mem,
  exact eq1.symm,
end

def fmk (y : unop U) : localization.at_prime y.1.as_ideal :=
mk (num hm hh y) ⟨denom hm hh y, denom.not_mem hm hh y⟩

lemma fmk.one (y : unop U) : fmk hm 1 y = 1 :=
begin
  unfold fmk,
  dsimp only,
  rw [show (1 : structure_sheaf.localizations (A⁰_ f_deg) y.val) =
    localization.mk 1 1, begin
      erw localization.mk_self 1,
    end, localization.mk_eq_mk', is_localization.eq],

  have eq1 := (hl hm 1 y).eq_num_div_denom,
  rw [hl.one, homogeneous_localization.one_val] at eq1,
  erw [show (1 : localization.at_prime ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) =
    mk 1 1,
      begin
        symmetry,
        convert localization.mk_self _,
        refl,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,

  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  rw [one_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [←subtype.val_eq_coe] at eq1,
  rw [← hl.one] at eq1,
  have eq2 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).denom * c) 
    = graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).num * c),
  { exact congr_arg _ eq1, },
  
  have eq3 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j) ((hl hm 1 y).denom * c)
    = (hl hm 1 y).denom * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 1 y).denom_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  have eq4 : graded_algebra.proj 𝒜 ((hl hm 1 y).deg + j)
    ((hl hm 1 y).num * c)
    = (hl hm 1 y).num * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 1 y).num_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  erw [eq3, eq4] at eq2,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  rw [submonoid.coe_one, one_mul, mul_one, ← subtype.val_eq_coe, ← subtype.val_eq_coe],
  dsimp only,

  unfold num denom,
  rw [subtype.ext_iff_val, degree_zero_part.mul_val, mk_mul, degree_zero_part.mul_val, mk_mul],
  congr' 1,
  exact calc (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m
          = (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = (hl hm 1 y).num * (hl hm 1 y).denom ^ m.pred * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : by ring_exp
      ... = ((hl hm 1 y).num * graded_algebra.proj 𝒜 j c) * ((hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by ring
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) * ((hl hm 1 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by rw eq2
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) ^ (1 + m.pred)
          : by ring_exp
      ... = ((hl hm 1 y).denom * graded_algebra.proj 𝒜 j c) ^ m
          : begin
            congr' 1,
            rw [add_comm],
            convert nat.succ_pred_eq_of_pos hm,
          end
      ... = _ : by rw mul_pow,
end

lemma fmk.zero (y : unop U) : fmk hm 0 y = 0 :=
begin
  unfold fmk,
  rw [show (0 : structure_sheaf.localizations (A⁰_ f_deg) y.val) =
    localization.mk 0 1, begin
      rw localization.mk_zero,
    end, localization.mk_eq_mk', is_localization.eq],
  dsimp only,

  have eq1 := (hl hm 0 y).eq_num_div_denom,
  rw [hl.zero, homogeneous_localization.zero_val] at eq1,
  erw [show (0 : localization.at_prime ((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1.as_homogeneous_ideal.to_ideal) =
    localization.mk 0 1,
      begin
        rw localization.mk_zero,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one] at eq1,
  simp only [←subtype.val_eq_coe] at eq1,
  dsimp only at eq1,

  change c ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ at hc1,
  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  rw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  replace eq1 := eq1.symm,
  have eq2 : graded_algebra.proj 𝒜 ((hl hm 0 y).deg + j) ((hl hm 0 y).num * c) = 0,
  { erw [eq1, linear_map.map_zero], },
  have eq3 : graded_algebra.proj 𝒜 ((hl hm 0 y).deg + j) ((hl hm 0 y).num * c)
    = (hl hm 0 y).num * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    exact (hl hm 0 y).num_mem,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, mk_zero],
    exact submodule.zero_mem _, },
    erw eq3 at eq2,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  unfold num,
  rw [subtype.ext_iff_val, degree_zero_part.mul_val, degree_zero_part.mul_val, degree_zero_part.mul_val, degree_zero_part.mul_val, degree_zero_part.zero_val, zero_mul, submonoid.coe_one, degree_zero_part.one_val, mul_one, zero_mul],
  simp only [← subtype.val_eq_coe],
  rw [mk_mul],
  dsimp only,
  convert mk_zero _,
  exact calc (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m
          = (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = (hl hm 0 y).num * (hl hm 0 y).denom ^ m.pred * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : by rw [pow_add, pow_one]
      ... = ((hl hm 0 y).num * graded_algebra.proj 𝒜 j c)
            * ((hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred) : by ring
      ... = 0 * ((hl hm 0 y).denom ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred) : by rw eq2
      ... = 0 : by rw zero_mul,
end

lemma fmk.add (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm (x + y) z = fmk hm x z + fmk hm y z :=
begin
  unfold fmk,
  rw [localization.add_mk],

  have eq_xz := (hl hm x z).eq_num_div_denom,
  have eq_yz := (hl hm y z).eq_num_div_denom,
  have eq_addz := (hl hm (x + y) z).eq_num_div_denom,
  rw [hl.add, homogeneous_localization.add_val, eq_xz, eq_yz, localization.add_mk, localization.mk_eq_mk', is_localization.eq] at eq_addz,
  obtain ⟨⟨c, hc⟩, eq_addz⟩ := eq_addz,
  rw [submonoid.coe_mul] at eq_addz,
  simp only [←subtype.val_eq_coe] at eq_addz,

  set d_x := (hl hm x z).denom with dx_eq,
  set n_x := (hl hm x z).num with nx_eq,
  set d_y := (hl hm y z).denom with dy_eq,
  set n_y := (hl hm y z).num with ny_eq,
  set d_xy := (hl hm (x + y) z).denom with dxy_eq,
  set n_xy := (hl hm (x + y) z).num with nxy_eq,
  set i_x := (hl hm x z).deg with ix_eq,
  set i_y := (hl hm y z).deg with iy_eq,
  set i_xy := (hl hm (x + y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_addz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  rw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  rw [submonoid.coe_mul],
  simp only [← subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val, degree_zero_part.add_val, mk_mul, add_mk],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_one, submonoid.mk_mul_mk, set_like.coe_mk, mul_one, ← pow_add],

  rw calc (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
          + f ^ (i_y + i_x) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
            + f ^ (i_x + i_y) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 4,
          rw add_comm,
        end
    ... = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 3,
          rw mul_add,
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y) * f ^ (i_xy + (i_x + i_y) + j)) : by ring
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_xy + (i_x + i_y) + j)))
        : begin
          congr' 1,
          rw [←pow_add],
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_y + i_x) + i_xy + j))
        : begin
          congr' 2,
          ring,
        end,
  congr' 1,
  suffices EQ : (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  { rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ m
          = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1)) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = n_xy * d_xy ^ m.pred * (d_x ^ m.pred * d_x * (d_y ^ m.pred * d_y))
            * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          : begin
            simp only [pow_add, pow_one],
          end
      ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
          : by ring
      ... = ((d_x * n_y + d_y * n_x) * d_xy * (graded_algebra.proj 𝒜 j) c)
            * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
          : by rw EQ
      ... = (d_x * n_y + d_y * n_x)
            * ((d_xy ^ m.pred * d_xy) * d_x ^ m.pred * d_y ^ m.pred
              * ((graded_algebra.proj 𝒜 j c) ^ m.pred * (graded_algebra.proj 𝒜 j c)))
          : by ring
      ... = (d_x * n_y + d_y * n_x)
            * (d_xy ^ m * d_x ^ m.pred * d_y ^ m.pred
              * (graded_algebra.proj 𝒜 j c) ^ m)
          : begin
            congr';
            conv_rhs { rw [show m = m.pred + 1, from (nat.succ_pred_eq_of_pos hm).symm] };
            rw [pow_add, pow_one],
          end
      ... = (d_x * n_y + d_y * n_x)
            * d_x ^ m.pred * d_y ^ m.pred * d_xy ^ m
            * (graded_algebra.proj 𝒜 j c) ^ m : by ring,
    congr',

    exact calc (d_x * n_y + d_y * n_x) * d_x ^ m.pred * d_y ^ m.pred
          = (d_y ^ m.pred * d_y) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x) * (n_y * d_y ^ m.pred)
          : by ring
      ... = (d_y ^ m.pred * d_y^1) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x ^ 1) * (n_y * d_y ^ m.pred)
          : by simp only [pow_one]
      ... = (d_y ^ (m.pred + 1)) * (n_x * d_x ^ m.pred) + (d_x ^ (m.pred + 1)) * (n_y * d_y ^ m.pred)
          : by simp only [pow_add]
      ... = d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)
          : begin
            congr';
            apply nat.succ_pred_eq_of_pos hm,
          end, },

  replace eq_addz := congr_arg (graded_algebra.proj 𝒜 ((i_x + i_y) + i_xy + j)) eq_addz,
  have eq1 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) ((d_x * n_y + d_y * n_x) * d_xy * c)
    = (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { apply set_like.graded_monoid.mul_mem,
      apply submodule.add_mem _ _ _,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm x z).denom_mem,
      exact (hl hm y z).num_mem,
      rw add_comm,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm y z).denom_mem,
      exact (hl hm x z).num_mem,
      exact (hl hm (x + y) z).denom_mem, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  erw eq1 at eq_addz,
  clear eq1,

  have eq2 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) (n_xy * (d_x * d_y) * c)
    = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { rw show i_x + i_y + i_xy = i_xy + (i_x + i_y), by ring,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm (x + y) z).num_mem,
      apply set_like.graded_monoid.mul_mem,
      exact (hl hm _ z).denom_mem,
      exact (hl hm _ z).denom_mem, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  erw eq2 at eq_addz,
  exact eq_addz,
end

lemma fmk.mul (x y : (pf_sheaf (Proj| (pbo f))).obj U) (z : unop U) :
  fmk hm (x * y) z = fmk hm x z * fmk hm y z :=
begin
  unfold fmk,
  rw [mk_mul],

  have eq_xz := (hl hm x z).eq_num_div_denom,
  have eq_yz := (hl hm y z).eq_num_div_denom,
  have eq_mulz := (hl hm (x * y) z).eq_num_div_denom,
  rw [hl.mul, homogeneous_localization.mul_val, eq_xz, eq_yz, mk_mul, mk_eq_mk', is_localization.eq] at eq_mulz,
  obtain ⟨⟨c, hc⟩, eq_mulz⟩ := eq_mulz,
  simp only [submonoid.coe_mul] at eq_mulz,
  simp only [← subtype.val_eq_coe] at eq_mulz,

  set d_x := (hl hm x z).denom with dx_eq,
  set n_x := (hl hm x z).num with nx_eq,
  set d_y := (hl hm y z).denom with dy_eq,
  set n_y := (hl hm y z).num with ny_eq,
  set d_xy := (hl hm (x * y) z).denom with dxy_eq,
  set n_xy := (hl hm (x * y) z).num with nxy_eq,
  set i_x := (hl hm x z).deg with ix_eq,
  set i_y := (hl hm y z).deg with iy_eq,
  set i_xy := (hl hm (x * y) z).deg with ixy_eq,

  unfold num denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_mulz ⊢,
  rw [localization.mk_eq_mk', is_localization.eq],

  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  erw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  simp only [submonoid.coe_mul],
  simp only [← subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val, mk_mul],
  simp only [mk_eq_mk', is_localization.eq],

  use 1,
  simp only [submonoid.coe_one, submonoid.coe_mul, mul_one],
  simp only [← subtype.val_eq_coe, ← pow_add],

  suffices EQ : n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,

  rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_x + i_y + i_xy + j)
        = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1))
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          all_goals { symmetry, apply nat.succ_pred_eq_of_pos hm, },
        end
    ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by rw EQ
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * graded_algebra.proj 𝒜 j c))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * (graded_algebra.proj 𝒜 j c)^1))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^(m.pred + 1)))
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy^1) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y) * ((d_xy^(m.pred + 1)) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : by ring_exp
    ... = (n_x * n_y) * (d_xy^m * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end,
  ring_nf,

  have INEQ : graded_algebra.proj 𝒜 j c ≠ 0,
  { intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  replace eq_mulz := congr_arg (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) eq_mulz,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq_mulz,
  exact eq_mulz,

  have : (hl hm x z * hl hm y z).num * (d_x * d_y) ∈ 𝒜 (i_xy + (i_x + i_y)),
  { apply set_like.graded_monoid.mul_mem,
    rw [← hl.mul],
    exact (hl hm (x * y) z).num_mem,
    apply set_like.graded_monoid.mul_mem,
    exact (hl hm x z).denom_mem,
    exact (hl hm y z).denom_mem, },
  convert this using 2,
  ring,

  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  exact (hl hm x z).num_mem,
  exact (hl hm y z).num_mem,
  rw [← hl.mul],
  exact (hl hm (x * y) z).denom_mem,

  exact INEQ,
end

namespace is_locally_quotient

variable (f_deg)
def open_set (V : opens Proj.T) : opens (Spec.T (A⁰_ f_deg)) :=
⟨homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) '' {z | z.1 ∈ V.1}, begin
  rw [homeomorph.is_open_image, is_open_induced_iff],
  refine ⟨V.1, V.2, _⟩,
  ext z, split; intro hz,
  { rw set.mem_preimage at hz,
    exact hz, },
  { rw set.mem_preimage,
    exact hz, }
end⟩

lemma open_set_is_subset
  (V : opens Proj.T) (y : unop U)
  (subset1 : V ⟶ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
            ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop) :
  (open_set 𝒜 hm f_deg V) ⟶ unop U := hom_of_le
begin
  have subset2 := le_of_hom subset1,
  rintros z z_mem,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  change z.1 ∈ _ at z_mem,
  specialize subset2 z_mem,
  obtain ⟨a, a_mem, eq2⟩ := subset2,
  erw set.mem_preimage at a_mem,
  rw homeo_of_iso_apply,
  change _ ∈ (unop U).val,
  convert a_mem,
  rw subtype.ext_iff_val,
  rw ←eq2,
  refl,
end

lemma mem_open_subset_of_inv_mem (V : opens Proj.T) (y : unop U)
  (mem1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) y.val).val ∈ V) :
  y.1 ∈ open_set 𝒜 hm f_deg V  :=
begin
  refine ⟨(Proj_iso_Spec_Top_component hm f_deg).inv y.1, mem1, _⟩,
  rw [homeo_of_iso_apply],
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

/--
For b ∈ 𝒜 i
z ∈ V and b ∉ z, then b^m / f^i ∉ forward f 
-/
lemma not_mem
  (V : opens Proj.T)
  -- (subset1 : V ⟶ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
  --           ((opens.map (Top_component hm f_deg).hom).op.obj U)).unop)
  (b : A) (degree : ℕ) (b_mem : b ∈ 𝒜 degree)
  (z : Proj.T| (pbo f))
  (z_mem : z.1 ∈ V.1) 
  (b_not_mem : b ∉ z.1.as_homogeneous_ideal) :
  (⟨localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩,
    ⟨degree, ⟨_, set_like.graded_monoid.pow_mem _ b_mem⟩, rfl⟩⟩ : A⁰_ f_deg) 
  ∉ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).as_ideal := λ rid,
begin
  classical,

  rw homeo_of_iso_apply at rid,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at rid,
  dsimp only at rid,

  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose after_clear_denominator hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (localization.mk (b^m) 1 : localization.away f) * localization.mk (f^N) 1
          = localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * localization.mk (f^degree) 1 * localization.mk (f^N) 1
          : begin
            congr,
            rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
            use 1,
            erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
          end
      ... = localization.mk (f^degree) 1 * localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
          : by ring
      ... = localization.mk (f^degree) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
          : begin
            erw eq1, ring,
          end
      ... = localization.mk (f^degree) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
      ... = localization.mk (f^degree) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
          : begin
            congr' 1,
            rw finset.mul_sum,
          end
      ... = localization.mk (f^degree) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
          : begin
            congr' 1,
            symmetry,
            convert finset.sum_attach,
            refl,
          end
      ... = localization.mk (f^degree) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            congr' 1,
            rw finset.sum_congr rfl (λ j hj, _),
            have eq2 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
            dsimp only at eq2,
            erw eq2,
            rw mul_comm,
          end
      ... = ∑ i in c.support.attach, (localization.mk (f^degree) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            rw finset.mul_sum,
          end
      ... = ∑ i in c.support.attach, localization.mk (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
          : begin
            rw finset.sum_congr rfl (λ j hj, _),
            erw [localization.mk_mul, one_mul],
          end
      ... = localization.mk (∑ i in c.support.attach, (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
          : begin
            induction c.support.attach using finset.induction_on with y s hy ih,
            rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
            rw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, ←subtype.val_eq_coe,
              show (1 : submonoid.powers f).1 = 1, from rfl, one_mul, one_mul, add_comm],
          end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^degree * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { apply b_not_mem,
    rw z.1.is_prime.pow_mem_iff_mem at H1,
    exact H1,
    exact hm, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  apply ideal.mul_mem_right,
  apply ideal.sum_mem,
  intros j hj,
  apply ideal.mul_mem_left,
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,
  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = localization.mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,
  have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
          = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
          : by erw hzz
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
          : by erw eq3
      ... = localization.mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
          : begin
            erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
          end,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
  dsimp only at eq6,
  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal,
  { apply ideal.mul_mem_right,
    apply ideal.mul_mem_right,
    apply ideal.mul_mem_left,
    exact mem3, },
  erw ←eq6 at mem4,
  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
end

include hm
lemma mk_proj_pow_not_mem
  (V : opens (projective_spectrum.Top 𝒜))
  (z : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)))
  (C : A) (j : ℕ) (hj : graded_algebra.proj 𝒜 j C ∉ z.1.as_homogeneous_ideal) :
  (localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f ^ j, ⟨j, rfl⟩⟩ : localization.away f) ∉
    ideal.span ((algebra_map A (away f)) '' ↑(projective_spectrum.as_homogeneous_ideal z.val)) :=
begin
  haveI : decidable_eq (away f) := classical.dec_eq _,

  intro rid,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
  obtain ⟨c, eq1⟩ := rid,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  obtain ⟨N, hN⟩ := clear_denominator (finset.image (λ i, c i * i.1) c.support),
  -- N is the common denom
  choose after_clear_denominator hacd using hN,
  have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  have eq3 := calc (localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) 1 : localization.away f) * localization.mk (f^N) 1
          = localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * localization.mk (f^j) 1 * localization.mk (f^N) 1
          : begin
            congr,
            rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
            use 1,
            erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
          end
      ... = localization.mk (f^j) 1 * localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f^j, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
          : by ring
      ... = localization.mk (f^j) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
          : begin
            erw eq1, ring,
          end
      ... = localization.mk (f^j) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
      ... = localization.mk (f^j) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
          : begin
            congr' 1,
            rw finset.mul_sum,
          end
      ... = localization.mk (f^j) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
          : begin
            congr' 1,
            symmetry,
            convert finset.sum_attach,
            refl,
          end
      ... = localization.mk (f^j) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            congr' 1,
            rw finset.sum_congr rfl (λ j hj, _),
            have eq2' := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
            dsimp only at eq2',
            erw eq2',
            rw mul_comm,
          end
      ... = ∑ i in c.support.attach, (localization.mk (f^j) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
          : begin
            rw finset.mul_sum,
          end
      ... = ∑ i in c.support.attach, localization.mk (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
          : begin
            rw finset.sum_congr rfl (λ j hj, _),
            erw [localization.mk_mul, one_mul],
          end
      ... = localization.mk (∑ i in c.support.attach, (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
          : begin
            induction c.support.attach using finset.induction_on with y s hy ih,
            rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
            erw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm],
          end,
  erw [localization.mk_mul, one_mul] at eq3,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
  erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
  dsimp only at eq3,
  suffices : (∑ i in c.support.attach, (f^j * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ z.1.as_homogeneous_ideal,
  erw ←eq3 at this,
  rcases z.1.is_prime.mem_or_mem this with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { apply hj,
    rw z.1.is_prime.pow_mem_iff_mem at H1,
    exact H1,
    exact hm, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  apply ideal.mul_mem_right,
  apply ideal.sum_mem,
  intros j hj,
  apply ideal.mul_mem_left,
  set g := classical.some j.1.2 with g_eq,
  have mem3 : g ∈ z.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
  have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2.symm,
  have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
  dsimp only at eq4,

  have eq5 : ∃ (a : A) (zz : ℕ), c j.1 = localization.mk a ⟨f^zz, ⟨zz, rfl⟩⟩,
  { induction (c j.1) using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨zz, rfl⟩⟩⟩,
    refine ⟨a, zz, rfl⟩, },
  obtain ⟨α, zz, hzz⟩ := eq5,

  have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
          = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
          : by erw hzz
      ... = (localization.mk α ⟨f^zz, ⟨zz, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
          : by erw eq3
      ... = localization.mk (α * g * f^N) ⟨f^zz, ⟨zz, rfl⟩⟩
          : begin
            erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
          end,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
  obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
  dsimp only at eq6,

  have mem4 : α * g * f ^ N * f ^ v ∈ z.1.as_homogeneous_ideal,
  { apply ideal.mul_mem_right,
    apply ideal.mul_mem_right,
    apply ideal.mul_mem_left,
    exact mem3, },
  erw ←eq6 at mem4,

  rcases z.1.is_prime.mem_or_mem mem4 with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  { exact H1 },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H2,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, },
  { exfalso,
    have mem3 := z.2,
    have mem4 := z.1.is_prime.mem_of_pow_mem _ H3,
    erw projective_spectrum.mem_basic_open at mem3,
    apply mem3,
    exact mem4, }
end

omit hm
lemma final_eq
  (d_hh n_hh a b C : A) (degree i_hh j : ℕ) (INEQ : graded_algebra.proj 𝒜 j C ≠ 0)
  (d_hh_mem : d_hh ∈ 𝒜 i_hh) (n_hh_mem : n_hh ∈ 𝒜 i_hh)
  (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree)
  (eq1 : n_hh * b * C = a * d_hh * C) : n_hh * b * graded_algebra.proj 𝒜 j C = a * d_hh * graded_algebra.proj 𝒜 j C :=
begin
  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq2,
  exact eq2,

  rw add_comm,
  apply set_like.graded_monoid.mul_mem,
  exact a_hom,
  exact d_hh_mem,
  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  exact n_hh_mem,
  exact b_hom,
  exact INEQ,
end

lemma inv_hom_mem_bo (V : opens Proj.T) (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U) (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val ∈ projective_spectrum.basic_open 𝒜 f :=
begin
  erw projective_spectrum.mem_basic_open,
  intro rid,
  change ∀ _, _ at rid,
  specialize rid m,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
  change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
  have rid2 : (1 : A⁰_ f_deg) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
  { convert rid,
    rw subtype.ext_iff_val,
    dsimp only,
    erw localization.mk_self (⟨f^m, ⟨_, rfl⟩⟩ : submonoid.powers f),
    refl, },
  rw homeo_of_iso_apply at rid2,
  apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
  rw ideal.eq_top_iff_one,
  exact rid2,
end

lemma inv_hom_mem2
  (V : opens Proj.T)
  (z : Proj.T| (pbo f))
  (subset2 : open_set 𝒜 hm f_deg V ⟶ unop U)
  (z_mem : z.1 ∈ V) :
  (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val ∈
  ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop :=
begin
  simp only [unop_op, functor.op_obj],
  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val with z'_eq,
  refine ⟨⟨z', _⟩, _, rfl⟩,
  have mem_z' : z' ∈ projective_spectrum.basic_open 𝒜 f,
  erw projective_spectrum.mem_basic_open,
  intro rid,
  erw z'_eq at rid,
  change ∀ _, _ at rid,
  specialize rid m,
  simp only [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same 𝒜 f_deg] at rid,
  change _ ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1 at rid,
  have rid2 : (1 : A⁰_ f_deg) ∈ ((homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z).1,
  { convert rid,
    rw subtype.ext_iff_val,
    dsimp only,
    erw localization.mk_self (⟨f^m, ⟨_, rfl⟩⟩ : submonoid.powers f),
    refl, },
  rw homeo_of_iso_apply at rid2,
  apply (((Proj_iso_Spec_Top_component hm f_deg).hom) z).is_prime.1,
  rw ideal.eq_top_iff_one,
  exact rid2,
  exact mem_z',
  erw [set.mem_preimage],
  have subset3 := le_of_hom subset2,
  suffices : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z', _⟩ ∈ open_set 𝒜 hm f_deg V,
  apply subset3,
  exact this,

  refine ⟨z, z_mem, _⟩,
  simp only [homeo_of_iso_apply],
  congr',
  rw subtype.ext_iff_val,
  dsimp only,
  rw z'_eq,
  change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg (Proj_iso_Spec_Top_component.to_Spec _ _ _)).1,
  congr', 
  symmetry,
  apply Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z,
end

end is_locally_quotient

variables (hm f_deg)
lemma fmk_is_locally_quotient (y : unop U) :
  ∃ (V : opens (Spec.T (A⁰_ f_deg))) (mem : y.val ∈ V) (i : V ⟶ unop U) (r s : (A⁰_ f_deg)),
    ∀ (z : V),
      ∃ (s_not_mem : s ∉ prime_spectrum.as_ideal z.val),
        fmk hm hh ⟨(i z).1, (i z).2⟩ = mk r ⟨s, s_not_mem⟩ :=
begin
  classical,

  obtain ⟨V, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, eq1⟩ := hh.2 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv y.1).1, inv_mem y⟩,
  set VVo : opens (Spec.T (A⁰_ f_deg)) := is_locally_quotient.open_set 𝒜 hm f_deg V with VVo_eq,
  have subset2 : VVo ⟶ unop U := is_locally_quotient.open_set_is_subset 𝒜 hm f_deg V y subset1,
  have y_mem1 : y.1 ∈ VVo,
  { convert is_locally_quotient.mem_open_subset_of_inv_mem 𝒜 hm f_deg V y mem1 },
  refine ⟨VVo, y_mem1, subset2,
    ⟨localization.mk (a * b^m.pred) ⟨f^degree, ⟨_, rfl⟩⟩, ⟨degree, ⟨_, begin
      have mem1 : b^m.pred ∈ 𝒜 (m.pred * degree) := set_like.graded_monoid.pow_mem _ b_mem,
      have mem2 := set_like.graded_monoid.mul_mem a_mem mem1,
      convert mem2,
      exact calc m * degree
              = (m.pred + 1) * degree
              : begin
                congr' 1,
                symmetry,
                apply nat.succ_pred_eq_of_pos hm,
              end
          ... = m.pred * degree + 1 * degree : by rw add_mul
          ... = m.pred * degree + degree : by rw one_mul
          ... = degree + m.pred * degree : by rw add_comm,
    end⟩, rfl⟩⟩,
    ⟨localization.mk (b^m) ⟨f^degree, ⟨_, rfl⟩⟩, ⟨degree, ⟨_, set_like.graded_monoid.pow_mem _ b_mem⟩, rfl⟩⟩, _⟩,

  rintros ⟨z, z_mem⟩,
  obtain ⟨z, z_mem, rfl⟩ := z_mem,
  specialize eq1 ⟨z.1, z_mem⟩,
  obtain ⟨b_not_mem, eq1⟩ := eq1,

  refine ⟨is_locally_quotient.not_mem 𝒜 hm f_deg V b degree b_mem z z_mem b_not_mem, _⟩,

  have eq2 := (hh.val (subset1 ⟨z.val, z_mem⟩)).eq_num_div_denom,
  dsimp only at eq1,
  rw [homogeneous_localization.ext_iff_val] at eq1,
  rw [eq2, homogeneous_localization.val_mk'] at eq1,
  simp only [← subtype.val_eq_coe] at eq1,
  rw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨C, hC⟩, eq1⟩ := eq1,
  unfold fmk,
  rw [localization.mk_eq_mk', is_localization.eq],
  simp only [←subtype.val_eq_coe] at eq1,
  set degree_hh := (hh.val (subset1 ⟨z.val, z_mem⟩)).deg with degree_hh_eq,
  have mem_C : ∃ (j : ℕ), graded_algebra.proj 𝒜 j C ∉ z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    apply rid, },
  obtain ⟨j, hj⟩ := mem_C,
  refine ⟨⟨⟨localization.mk ((graded_algebra.proj 𝒜 j C)^m) ⟨f^j, ⟨_, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩, _⟩, _⟩,
  { change _ ∉ _,
    simp only [← subtype.val_eq_coe],
    erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    apply is_locally_quotient.mk_proj_pow_not_mem hm V z C j hj, },

  set z' := (((Proj_iso_Spec_Top_component hm f_deg).inv)
    (subset2 ⟨(homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg)) z, begin
    erw [set.mem_preimage],
    refine ⟨z, z_mem, rfl⟩,
  end⟩).val).val with z'_eq,

  have z'_mem : z' ∈ (((@opens.open_embedding Proj.T) (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj U)).unop,
  { convert is_locally_quotient.inv_hom_mem2 𝒜 hm f_deg V z subset2 z_mem },

  have eq_pt : (subset1 ⟨z.1, z_mem⟩) = ⟨z', z'_mem⟩,
  { rw subtype.ext_iff_val,
    change z.1 = (Proj_iso_Spec_Top_component.from_Spec hm f_deg (Proj_iso_Spec_Top_component.to_Spec m f_deg _)).1,
    congr', 
    symmetry,
    apply Proj_iso_Spec_Top_component.from_Spec_to_Spec 𝒜 hm f_deg z, },
  erw [eq_pt] at eq1,

  unfold num denom,
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val, localization.mk_mul],
  rw [localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [submonoid.coe_mul, submonoid.coe_one],
  simp only [←subtype.val_eq_coe, one_mul, mul_one, ←pow_add],

  set d_hh := (hh.val ⟨z', z'_mem⟩).denom with d_hh_eq,
  set n_hh := (hh.val ⟨z', z'_mem⟩).num with n_hh_eq,
  set i_hh := (hh.val ⟨z', z'_mem⟩).deg with i_hh_eq,
  simp only [←d_hh_eq, ←n_hh_eq, ←i_hh_eq] at eq1,

  suffices : n_hh * d_hh ^ m.pred * b ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree + i_hh + j)
    = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (i_hh + degree + j),
  convert this,

  suffices EQ : n_hh * b * graded_algebra.proj 𝒜 j C = a * d_hh * graded_algebra.proj 𝒜 j C,
  erw calc n_hh * d_hh ^ m.pred * b ^ m * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree + i_hh + j)
        = n_hh * d_hh ^ m.pred * b ^ (m.pred + 1) * (graded_algebra.proj 𝒜 j) C^(m.pred + 1) * f^(degree + i_hh + j)
        : begin
          congr';
          symmetry;
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_hh * d_hh ^ m.pred * (b ^ m.pred * b) * ((graded_algebra.proj 𝒜 j C) ^ m.pred * (graded_algebra.proj 𝒜 j C)) * f^(degree + i_hh + j)
        : begin
          congr',
          all_goals { rw [pow_add, pow_one], },
        end
    ... = (n_hh * b * graded_algebra.proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * (graded_algebra.proj 𝒜 j C)^m.pred) * f^(degree + i_hh + j)  : by ring
    ... = (a * d_hh * graded_algebra.proj 𝒜 j C) * (d_hh ^ m.pred * b ^ m.pred * (graded_algebra.proj 𝒜 j C)^m.pred) * f^(degree + i_hh + j)  : by rw EQ
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh) * ((graded_algebra.proj 𝒜 j C)^m.pred * graded_algebra.proj 𝒜 j C) * f^(degree + i_hh + j)  : by ring
    ... = a * b ^ m.pred * (d_hh ^ m.pred * d_hh^1) * ((graded_algebra.proj 𝒜 j C)^m.pred * graded_algebra.proj 𝒜 j C ^ 1) * f^(degree + i_hh + j)
        : by rw [pow_one, pow_one]
    ... =  a * b ^ m.pred * (d_hh ^ (m.pred + 1)) * ((graded_algebra.proj 𝒜 j C)^(m.pred + 1)) * f^(degree + i_hh + j)
        : by simp only [pow_add]
    ... = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j C)^m * f^(degree + i_hh + j)
        : begin
          congr',
          all_goals { apply nat.succ_pred_eq_of_pos hm, },
        end
    ... = a * b ^ m.pred * d_hh ^ m * (graded_algebra.proj 𝒜 j C)^m * f^(i_hh + degree + j)
        : begin
          congr' 1,
          rw add_comm i_hh degree,
        end,
  have INEQ : graded_algebra.proj 𝒜 j C ≠ 0,
  { intro rid,
    apply hj,
    rw rid,
    exact submodule.zero_mem _, },

  have eq2 := congr_arg (graded_algebra.proj 𝒜 (i_hh + degree + j)) eq1,
  rw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq2,
  exact eq2,

  rw add_comm,
  apply set_like.graded_monoid.mul_mem,
  exact a_mem,
  exact (hh.val ⟨z', z'_mem⟩).denom_mem,
  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  exact (hh.val ⟨z', z'_mem⟩).num_mem,
  exact b_mem,
  exact INEQ,
end

variable (U)
def to_fun : (pf_sheaf (Proj| (pbo f))).obj U ⟶ (Spec (A⁰_ f_deg)).presheaf.obj U := 
{ to_fun := λ hh, ⟨λ y, fmk hm hh y, begin
    rw algebraic_geometry.structure_sheaf.is_locally_fraction_pred',
    exact fmk_is_locally_quotient hm f_deg hh,
  end⟩,
  map_one' := begin 
    rw subtype.ext_iff_val, 
    dsimp only, 
    ext y, 
    rw [fmk.one hm],
    convert pi.one_apply _,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff_val, 
    dsimp only, 
    ext z, 
    rw [fmk.mul hm],
    change _ * _ = _ * _,
    dsimp only,
    refl,
  end,
  map_zero' := begin
    rw subtype.ext_iff_val, 
    dsimp only, 
    ext y, 
    rw [fmk.zero hm],
    convert pi.zero_apply _,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff_val,
    dsimp only,
    ext z,
    rw [fmk.add hm],
    change _ + _ = fmk hm x z + fmk hm y z,
    dsimp only,
    refl
  end }

end to_Spec

section

def to_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m):
  ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf) ⟶ (Spec (A⁰_ f_deg)).presheaf :=
{ app := λ U, to_Spec.to_fun hm f_deg U,
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    refl,
  end }

end

namespace from_Spec

open algebraic_geometry

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec (A⁰_ f_deg)))ᵒᵖ) 
variables (hh : (Spec (A⁰_ f_deg)).presheaf.obj V)
variables (y : ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj 
  ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop)

lemma data_prop1 : y.1 ∈ (pbo f) :=
begin
  obtain ⟨⟨a, ha1⟩, -, ha2⟩ := y.2,
  rw ← ha2,
  exact ha1,
end
-- -- ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj 
-- --  ((opens.map (Top_component hm f_deg).hom).op.obj V)).unop = h⁻¹ V
-- example (z : Proj.T| (pbo f)) (h: (Top_component hm f_deg).hom z ∈ unop V) : 
--   z.1 ∈ ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj 
--   ((opens.map (Top_component hm f_deg).hom).op.obj V)).unop.1 :=
-- begin
--   refine ⟨_, _, rfl⟩,
--   simp only [functor.op_obj, unop_op, opens.mem_coe],
--   erw opens.map_obj,
--   change _ ∈ _ ⁻¹' _,
--   dsimp only,
--   erw set.mem_preimage,
--   exact h,
--   exact V.unop.2,
-- end

lemma data_prop2 :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 hm f_deg V y⟩ ∈ unop V :=
begin
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
  erw set.mem_preimage at ha2,
  convert ha2,
  rw ← ha3,
  refl,
end

variable {V}
def data : structure_sheaf.localizations (A⁰_ f_deg) 
  ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩) :=
hh.1 ⟨_, data_prop2 _ _ _ _⟩

lemma data.one :
  data hm f_deg (1 : (Spec (A⁰_ f_deg)).presheaf.obj V) = 1 := rfl

lemma data.zero :
  data hm f_deg (0 : (Spec (A⁰_ f_deg)).presheaf.obj V) = 0 := rfl

lemma data.add_apply (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) (z):
  data hm f_deg (x + y) z = data hm f_deg x z + data hm f_deg y z := rfl

lemma data.mul_apply (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) (z):
  data hm f_deg (x * y) z = data hm f_deg x z * data hm f_deg y z := rfl

private lemma data.exist_rep 
  (data : structure_sheaf.localizations (A⁰_ f_deg) ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩)) :
  ∃ (a : A⁰_ f_deg) (b : ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal.prime_compl),
  data = mk a b :=
begin
  induction data using localization.induction_on with d,
  rcases d with ⟨a, b⟩,
  refine ⟨a, b, rfl⟩,
end

def data.num : A⁰_ f_deg :=
classical.some $ data.exist_rep hm f_deg y (data hm f_deg hh y)

def data.denom : A⁰_ f_deg :=
(classical.some $ classical.some_spec $ data.exist_rep hm f_deg y (data hm f_deg hh y)).1

lemma data.denom_not_mem : 
  (data.denom hm f_deg hh y) ∉ ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, data_prop1 _ _ _ _⟩).as_ideal :=
(classical.some $ classical.some_spec $ data.exist_rep hm f_deg y (data hm f_deg hh y)).2

lemma data.eq_num_div_denom :
  (data hm f_deg hh y) = 
  localization.mk (data.num hm f_deg hh y) ⟨data.denom hm f_deg hh y, data.denom_not_mem hm f_deg hh y⟩ :=
begin 
  rw classical.some_spec (classical.some_spec (data.exist_rep hm f_deg y (data hm f_deg hh y))), 
  congr, 
  rw subtype.ext_iff_val, 
  refl,
end

def num : A :=
degree_zero_part.num (data.num hm f_deg hh y) * f^(degree_zero_part.deg (data.denom hm f_deg hh y))

lemma num.mem :
  (num hm f_deg hh y) ∈ 
    𝒜 (m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y))) :=
mul_mem (degree_zero_part.num_mem _) $ begin
  convert (set_like.graded_monoid.pow_mem (degree_zero_part.deg (data.denom hm f_deg hh y)) f_deg) using 1,
  rw mul_comm,
  refl,
end

def denom : A :=
degree_zero_part.num (data.denom hm f_deg hh y) * f^(degree_zero_part.deg (data.num hm f_deg hh y))

lemma denom.mem :
  (denom hm f_deg hh y) ∈ 
  𝒜 (m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y))) :=
begin
  change _ * _ ∈ _,
  rw mul_comm,
  apply set_like.graded_monoid.mul_mem,
  { rw mul_comm,
    exact set_like.graded_monoid.pow_mem (degree_zero_part.deg (data.num hm f_deg hh y)) f_deg, },
  { apply degree_zero_part.num_mem, },
end

lemma denom_not_mem :
  denom hm f_deg hh y ∉ y.1.as_homogeneous_ideal := λ rid,
begin
  rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
  { have mem1 := data.denom_not_mem hm f_deg hh y,
    have eq1 := degree_zero_part.eq (data.denom hm f_deg hh y),
    dsimp only at mem1,
    change _ ∉ _ at mem1,
    apply mem1,
    change
      (data.denom hm f_deg hh y) ∈ ((Proj_iso_Spec_Top_component.to_Spec.carrier f_deg) ⟨y.1, _⟩),
    rw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
    rw eq1,
    convert ideal.mul_mem_left _ _ _,
    work_on_goal 2
    { exact mk 1 ⟨f^degree_zero_part.deg (data.denom hm f_deg hh y), ⟨_, rfl⟩⟩ },
    work_on_goal 2
    { exact mk (degree_zero_part.num (data.denom hm f_deg hh y)) 1 },
    { rw [mk_mul, one_mul, mul_one], },
    { apply ideal.subset_span,
      exact ⟨_, H1, rfl⟩ }, },
  { replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
    obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
    erw projective_spectrum.mem_basic_open at ha1,
    apply ha1,
    convert H2, }
end

variable (V)
def bmk : homogeneous_localization 𝒜 y.1.as_homogeneous_ideal.to_ideal := quotient.mk' 
{ deg := m * (degree_zero_part.deg (data.num hm f_deg hh y)) 
      + m * (degree_zero_part.deg (data.denom hm f_deg hh y)),
  num := ⟨num hm f_deg hh y, num.mem hm f_deg hh y⟩,
  denom := ⟨denom hm f_deg hh y, denom.mem hm f_deg hh y⟩,
  denom_not_mem := denom_not_mem hm f_deg hh y }

lemma bmk_one :
  bmk hm f_deg V 1 = 1 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.one_apply,
  unfold bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.one_val],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 1 y,
  rw [data.one, pi.one_apply] at eq1,
  replace eq1 := eq1.symm,
  rw [show (1 : structure_sheaf.localizations (A⁰_ f_deg)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 1 1,
    by erw localization.mk_self 1, localization.mk_eq_mk'] at eq1,
  replace eq1 := (@@is_localization.eq _ _ _ _).mp eq1,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, eq1⟩ := eq1,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  simp only [←subtype.val_eq_coe, mul_one, one_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  dsimp only at C_degree_zero hC,

  have eq_num := degree_zero_part.eq (data.num hm f_deg 1 y),
  have eq_denom := degree_zero_part.eq (data.denom hm f_deg 1 y),

  simp only [subtype.val_eq_coe, submonoid.coe_one, mul_one] at eq1,
  rw subtype.ext_iff_val at eq1,
  simp only [degree_zero_part.mul_val] at eq1,
  erw [eq_num, eq_denom, localization.mk_mul, localization.mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl, ←pow_add] at eq1,

  have C_not_mem : C ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨_, rid, rfl⟩, },

  rw [show (1 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = mk (1 : _) 1, by erw mk_self 1, mk_eq_mk', is_localization.eq],
  use C * (f^l * f^n1),
  { intros rid,
    rcases y.1.is_prime.mem_or_mem rid with H1 | H3,
    exact C_not_mem H1,
    rw ←pow_add at H3,
    replace H3 := y.1.is_prime.mem_of_pow_mem _ H3,
    apply y_mem,
    exact H3, },

  simp only [submonoid.coe_one, one_mul, mul_one],
  simp only [←subtype.val_eq_coe],

  rw calc degree_zero_part.num (data.num hm f_deg 1 y)
        * f ^ degree_zero_part.deg (data.denom hm f_deg 1 y)
        * (C * (f ^ l * f ^ n1))
      = degree_zero_part.num (data.num hm f_deg 1 y) * C
        * f ^ (degree_zero_part.deg (data.denom hm f_deg 1 y) + l)
        * f^n1 : by ring_exp,
  rw [eq1, pow_add],
  ring,
end

lemma bmk_zero :
  bmk hm f_deg V 0 = 0 :=
begin
  ext1 y,
  have y_mem : y.val ∈ (pbo f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := y.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = y.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.zero_apply,
  unfold bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.zero_val],
  simp only [← subtype.val_eq_coe],
  rw [show (0 : localization.at_prime y.1.as_homogeneous_ideal.to_ideal) = localization.mk 0 1,
    by erw localization.mk_zero],
  dsimp only,
  unfold num denom,

  have eq1 := data.eq_num_div_denom hm f_deg 0 y,
  rw [data.zero, pi.zero_apply] at eq1,
  replace eq1 := eq1.symm,
  erw [show (0 : structure_sheaf.localizations (A⁰_ f_deg)
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨y.val, y_mem⟩)) = localization.mk 0 1,
    by erw localization.mk_zero, localization.mk_eq_mk', is_localization.eq] at eq1,

  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, eq1⟩ := eq1,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  simp only [submonoid.coe_one, mul_one, one_mul] at eq1,
  simp only [←subtype.val_eq_coe, zero_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq],
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  dsimp only at C_degree_zero hC,

  have eq_num := degree_zero_part.eq (data.num hm f_deg 0 y),
  have eq_denom := degree_zero_part.eq (data.denom hm f_deg 0 y),

  rw subtype.ext_iff_val at eq1,
  simp only [degree_zero_part.mul_val] at eq1,
  rw [eq_num, degree_zero_part.zero_val,
    show (0 : localization.away f) = localization.mk 0 1, by rw localization.mk_zero,
    localization.mk_mul] at eq1,
  simp only [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, eq1⟩ := eq1,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl, ←pow_add,
    show (1 : submonoid.powers f).1 = 1, from rfl, mul_one, zero_mul] at eq1,

  have C_not_mem : C ∉ y.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨C, rid, rfl⟩, },

  use C * f^n1,
  { intro rid,
    rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
    apply y_mem,
    exact H2, },

  simp only [submonoid.coe_one, zero_mul, mul_one],
  simp only [← subtype.val_eq_coe],

  rw calc degree_zero_part.num (data.num hm f_deg 0 y)
        * f ^ degree_zero_part.deg (data.denom hm f_deg 0 y)
        * (C * f ^ n1)
      = degree_zero_part.num (data.num hm f_deg 0 y)
        * C * f ^ n1
        * f ^ degree_zero_part.deg (data.denom hm f_deg 0 y)
      : by ring,
  rw [eq1, zero_mul],
end

lemma bmk_add (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) :
  bmk hm f_deg V (x + y) = bmk hm f_deg V x + bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := z.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = z.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid },

  rw pi.add_apply,
  unfold bmk,
  simp only [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.add_val, ←subtype.val_eq_coe],
  unfold num denom,
  dsimp only,

  have add_eq := data.eq_num_div_denom hm f_deg (x + y) z,
  rw [data.add_apply, data.eq_num_div_denom, data.eq_num_div_denom, add_mk] at add_eq,
  simp only [localization.mk_eq_mk'] at add_eq,
  erw is_localization.eq at add_eq,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, add_eq⟩ := add_eq,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  change _ ∉ _ at hC, 
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  simp only at hC,
  simp only [submonoid.coe_mul] at add_eq,
  simp only [←subtype.val_eq_coe] at add_eq,
  rw subtype.ext_iff_val at add_eq,
  simp only [degree_zero_part.add_val, degree_zero_part.mul_val] at add_eq,

  have C_not_mem : C ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    exact ⟨C, rid, rfl⟩, },

  simp only [degree_zero_part.eq, localization.mk_mul, localization.add_mk, ←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl] at add_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at add_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, add_eq⟩ := add_eq,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl] at add_eq,

  set a_xy : A := degree_zero_part.num (data.num hm f_deg (x + y) z) with a_xy_eq,
  set i_xy : ℕ := degree_zero_part.deg (data.num hm f_deg (x + y) z) with i_xy_eq,
  set b_xy : A := degree_zero_part.num (data.denom hm f_deg (x + y) z) with b_xy_eq,
  set j_xy : ℕ := degree_zero_part.deg (data.denom hm f_deg (x + y) z) with j_xy_eq,

  set a_x : A := degree_zero_part.num (data.num hm f_deg x z) with a_x_eq,
  set i_x : ℕ := degree_zero_part.deg (data.num hm f_deg x z) with i_x_eq,
  set b_x : A := degree_zero_part.num (data.denom hm f_deg x z) with b_x_eq,
  set j_x : ℕ := degree_zero_part.deg (data.denom hm f_deg x z) with j_x_eq,

  set a_y : A := degree_zero_part.num (data.num hm f_deg y z) with a_y_eq,
  set i_y : ℕ := degree_zero_part.deg (data.num hm f_deg y z) with i_y_eq,
  set b_y : A := degree_zero_part.num (data.denom hm f_deg y z) with b_y_eq,
  set j_y : ℕ := degree_zero_part.deg (data.denom hm f_deg y z) with j_y_eq,

  simp only [←a_xy_eq, ←i_xy_eq, ←b_xy_eq, ←j_xy_eq, ←a_x_eq, ←i_x_eq, ←b_x_eq, ←j_x_eq, ←a_y_eq, ←b_y_eq, ←i_y_eq, ←j_y_eq] at add_eq ⊢,

  rw localization.add_mk,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : z.1.as_homogeneous_ideal.to_ideal.prime_compl), α * β = ⟨α.1 * β.1, begin
      intro rid,
      rcases z.1.is_prime.mem_or_mem rid,
      apply α.2 h,
      apply β.2 h,
    end⟩,
    begin
      intros α β,
      simp only [subtype.ext_iff_val],
      refl,
    end,
    show b_x * f ^ i_x * (a_y * f ^ j_y) = a_y * b_x * f ^ (i_x + j_y),
    begin
      rw pow_add, ring,
    end,
    show b_y * f ^ i_y * (a_x * f ^ j_x) = a_x * b_y * f ^ (i_y + j_x),
    begin
      rw pow_add, ring
    end,
    show b_x * f ^ i_x * (b_y * f ^ i_y) = b_x * b_y * f ^ (i_x + i_y),
    begin
      rw pow_add, ring
    end],
  rw [calc (f ^ j_x * f ^ i_y * (b_y * a_x) + f ^ j_y * f ^ i_x * (b_x * a_y)) * b_xy * C
          * (f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1
        = ((f ^ j_x * f ^ i_y) * (b_y * a_x) + (f ^ j_y * f ^ i_x) * (b_x * a_y)) * b_xy * C
          * ((f ^ i_xy * (f ^ j_x * f ^ j_y) * f ^ l) * f ^ n1) : by ring
    ... = ((f ^ (j_x + i_y)) * (b_y * a_x) + (f ^ (j_y + i_x)) * (b_x * a_y)) * b_xy * C
          * f ^ ((((i_xy + (j_x + j_y))) + l) + n1)
        : begin
          congr',
          all_goals { repeat { rw pow_add } },
        end,
      calc a_xy * (b_x * b_y) * C * (f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1
        = a_xy * (b_x * b_y) * C * ((f ^ j_x * f ^ i_y * (f ^ j_y * f ^ i_x) * f ^ j_xy * f ^ l) * f ^ n1) : by ring
    ... = a_xy * (b_x * b_y) * C * f ^ (((((j_x + i_y) + (j_y + i_x)) + j_xy) + l) + n1) : by simp only [pow_add]] at add_eq,

  simp only [localization.mk_eq_mk', is_localization.eq],
  refine ⟨⟨C * f ^ ((j_x + j_y) + l + n1), begin
    intro rid,
    rcases z.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
    apply z_mem H2,
  end⟩, _⟩,
  simp only [←subtype.val_eq_coe],

  rw [calc (a_y * b_x * f ^ (i_x + j_y) + a_x * b_y * f ^ (i_y + j_x)) * (b_xy * f ^ i_xy)
          * (C * f ^ ((j_x + j_y) + l + n1))
        = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C
          * (f ^ i_xy * f ^ ((j_x + j_y) + l + n1)) : by ring
    ... = (f ^ (i_y + j_x) * (b_y * a_x) +  f ^ (i_x + j_y) * (b_x * a_y)) * b_xy * C
          * (f ^ (i_xy + ((j_x + j_y) + l + n1))) : by simp only [pow_add]
    ... = (f ^ (j_x + i_y) * (b_y * a_x) +  f ^ (j_y + i_x) * (b_x * a_y)) * b_xy * C
          * (f ^ (i_xy + (j_x + j_y) + l + n1))
        : begin
          congr' 1,
          congr' 5,
          all_goals { simp only [add_comm, add_assoc], },
        end, add_eq],
  simp only [pow_add],
  ring,
end

lemma bmk_mul (x y : (Spec (A⁰_ f_deg)).presheaf.obj V) :
  bmk hm f_deg V (x * y) = bmk hm f_deg V x * bmk hm f_deg V y :=
begin
  ext1 z,
  have z_mem : z.val ∈ (projective_spectrum.basic_open 𝒜 f).val,
  { erw projective_spectrum.mem_basic_open,
    intro rid,
    have mem1 := z.2,
    erw set.mem_preimage at mem1,
    obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
    change a = z.1 at ha2,
    erw set.mem_preimage at ha,
    erw ←ha2 at rid,
    apply ha1,
    exact rid, },

  rw pi.mul_apply,
  unfold bmk,
  simp only [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk', homogeneous_localization.mul_val, ← subtype.val_eq_coe],
  unfold num denom,

  have mul_eq := data.eq_num_div_denom hm f_deg (x * y) z,
  rw [data.mul_apply, data.eq_num_div_denom, data.eq_num_div_denom, localization.mk_mul] at mul_eq,
  simp only [←subtype.val_eq_coe, localization.mk_eq_mk'] at mul_eq,
  erw is_localization.eq at mul_eq,
  obtain ⟨⟨⟨C, C_degree_zero⟩, hC⟩, mul_eq⟩ := mul_eq,
  induction C using localization.induction_on with 𝔻,
  obtain ⟨C, ⟨_, ⟨l, rfl⟩⟩⟩ := 𝔻,
  change _ ∉ _ at hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff at hC,
  simp only at hC,
  simp only [←subtype.val_eq_coe] at mul_eq,
  rw subtype.ext_iff_val at mul_eq,

  have C_not_mem : C ∉ z.1.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ l, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^l, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    erw eq1 at hC,
    apply hC,
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    exact ⟨C, rid, rfl⟩, },

  simp only [degree_zero_part.mul_val, degree_zero_part.add_val,
    show ∀ (α β : (prime_spectrum.as_ideal (((Proj_iso_Spec_Top_component hm f_deg).hom)
      ⟨z.val, z_mem⟩)).prime_compl),
      (α * β).1 = α.1 * β.1, from λ _ _, rfl] at mul_eq,
  simp only [degree_zero_part.eq, localization.mk_mul, localization.add_mk, ←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl] at mul_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at mul_eq,
  obtain ⟨⟨_, ⟨n1, rfl⟩⟩, mul_eq⟩ := mul_eq,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl] at mul_eq,

  set a_xy : A := degree_zero_part.num (data.num hm f_deg (x * y) z) with a_xy_eq,
  set i_xy : ℕ := degree_zero_part.deg (data.num hm f_deg (x * y) z) with i_xy_eq,
  set b_xy : A := degree_zero_part.num (data.denom hm f_deg (x * y) z) with b_xy_eq,
  set j_xy : ℕ := degree_zero_part.deg (data.denom hm f_deg (x * y) z) with j_xy_eq,

  set a_x : A := degree_zero_part.num (data.num hm f_deg x z) with a_x_eq,
  set i_x : ℕ := degree_zero_part.deg (data.num hm f_deg x z) with i_x_eq,
  set b_x : A := degree_zero_part.num (data.denom hm f_deg x z) with b_x_eq,
  set j_x : ℕ := degree_zero_part.deg (data.denom hm f_deg x z) with j_x_eq,

  set a_y : A := degree_zero_part.num (data.num hm f_deg y z) with a_y_eq,
  set i_y : ℕ := degree_zero_part.deg (data.num hm f_deg y z) with i_y_eq,
  set b_y : A := degree_zero_part.num (data.denom hm f_deg y z) with b_y_eq,
  set j_y : ℕ := degree_zero_part.deg (data.denom hm f_deg y z) with j_y_eq,

  simp only [←a_xy_eq, ←i_xy_eq, ←b_xy_eq, ←j_xy_eq, ←a_x_eq, ←i_x_eq, ←b_x_eq, ←j_x_eq, ←a_y_eq, ←b_y_eq, ←i_y_eq, ←j_y_eq] at mul_eq ⊢,
  rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
  refine ⟨⟨C * f^(l + n1), begin
    intro rid,
    rcases z.1.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
    apply z_mem H2,
  end⟩, _⟩,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : z.1.as_homogeneous_ideal.to_ideal.prime_compl), (α * β).1 = α.1 * β.1,
    from λ _ _, rfl],
  simp only [pow_add],
  ring_nf at mul_eq ⊢,
  rw mul_eq,
end

namespace is_locally_quotient

variable {V}
lemma mem_pbo : y.1 ∈ pbo f :=
begin
  rw projective_spectrum.mem_basic_open,
  intro rid,
  have mem1 := y.2,
  erw set.mem_preimage at mem1,
  obtain ⟨⟨a, ha1⟩, ha, ha2⟩ := mem1,
  erw set.mem_preimage at ha,
  erw ←ha2 at rid,
  apply ha1,
  exact rid,
end

lemma hom_apply_mem :
  (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, mem_pbo hm f_deg y⟩ ∈ unop V := 
begin
  obtain ⟨a, ha1, ha2⟩ := y.2,
  erw set.mem_preimage at ha1,
  change ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, _⟩) ∈ (unop V).1,
  convert ha1,
  rw subtype.ext_iff_val,
  exact ha2.symm,
end

def Uo (VV : opens (Spec.T (A⁰_ f_deg))) :
  opens (projective_spectrum.Top 𝒜) :=
⟨{x | ∃ x' : homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg) ⁻¹' VV.1, x = x'.1.1}, begin
  have O1 := (homeomorph.is_open_preimage (homeo_of_iso (Proj_iso_Spec_Top_component hm f_deg))).2 VV.2,
  rw is_open_induced_iff at O1,
  obtain ⟨s, Os, set_eq1⟩ := O1,
  have O2 : is_open (s ∩ (projective_spectrum.basic_open 𝒜 f).1),
  apply is_open.inter Os (projective_spectrum.basic_open 𝒜 f).2,
  convert O2,
  ext γ, split; intros hγ,
  { obtain ⟨x', rfl⟩ := hγ,
    have mem1 := x'.2,
    simp only [←set_eq1] at mem1,
    erw set.mem_preimage at mem1,
    refine ⟨mem1, _⟩,
    have mem2 := x'.2,
    rw set.mem_preimage at mem2,
    intro rid,
    have mem3 : (⟨localization.mk f ⟨f^1, ⟨_, rfl⟩⟩, ⟨1, ⟨_, by simpa [mul_one] using f_deg⟩, rfl⟩⟩ : A⁰_ f_deg) ∈ ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
    { erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      change (localization.mk f ⟨f^1, ⟨_, rfl⟩⟩ : localization.away f) ∈ ideal.span _,
      convert ideal.mul_mem_left _ _ _,
      work_on_goal 2
      { exact mk 1 ⟨f^1, ⟨_, rfl⟩⟩ },
      work_on_goal 2
      { exact mk f 1 },
      { rw [mk_mul, one_mul, mul_one], },
      { apply ideal.subset_span,
        refine ⟨f, rid, rfl⟩, } },
    have mem4 : (1 : A⁰_ f_deg) ∈ ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).as_ideal,
    { convert mem3,
      rw [subtype.ext_iff_val, degree_zero_part.one_val],
      dsimp only,
      symmetry,
      convert localization.mk_self _,
      erw [←subtype.val_eq_coe],
      dsimp only,
      rw pow_one, },
    apply ((Proj_iso_Spec_Top_component hm f_deg).hom x'.1).is_prime.1,
    rw ideal.eq_top_iff_one,
    exact mem4, },

  { rcases hγ with ⟨hγ1, hγ2⟩,
    use ⟨γ, hγ2⟩,
    rw [←set_eq1, set.mem_preimage],
        convert hγ1, }
end⟩

lemma subset2 (VV : opens (Spec.T (A⁰_ f_deg)))
  (subset1 : VV ⟶ unop V) :
  Uo hm f_deg VV ⟶
  (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop) :=
begin
  apply hom_of_le,
  intros γ γ_mem,
  change γ ∈ _ at γ_mem,
  replace subset3 := le_of_hom subset1,
  obtain ⟨⟨γ, γ_mem⟩, rfl⟩ := γ_mem,
  erw set.mem_preimage at γ_mem,
  refine ⟨γ, _, _⟩,
  erw set.mem_preimage,
  apply subset3,
  exact γ_mem,
  rw subtype.ext_iff_val,
  dsimp only,
  rw show (opens.inclusion _ γ = γ.1), from rfl,
end

end is_locally_quotient

lemma is_locally_quotient :
  ∃ (U : opens _) (mem : y.val ∈ U)
    (subset1 : U ⟶
      (((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))
    (a b : A) (degree : ℕ) (a_hom : a ∈ 𝒜 degree) (b_hom : b ∈ 𝒜 degree),
    ∀ (x : U),
      ∃ (s_nin : b ∉ projective_spectrum.as_homogeneous_ideal x.val),
        (bmk hm f_deg V hh ⟨x.1, (subset1 x).2⟩).val = mk a ⟨b, s_nin⟩ :=
begin
  have y_mem : y.val ∈ projective_spectrum.basic_open 𝒜 f,
  { convert is_locally_quotient.mem_pbo hm f_deg y, },

  have hom_y_mem : (Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩ ∈ unop V,
  { convert is_locally_quotient.hom_apply_mem hm f_deg y, },
  have is_local := hh.2,
  rw structure_sheaf.is_locally_fraction_pred' at is_local,
  specialize is_local ⟨(Proj_iso_Spec_Top_component hm f_deg).hom ⟨y.1, y_mem⟩, hom_y_mem⟩,
  obtain ⟨VV, hom_y_mem_VV, subset1, ⟨α, ⟨l1, ⟨α', α'_mem⟩, rfl⟩⟩, ⟨β, ⟨l2, ⟨β', β'_mem⟩, rfl⟩⟩, is_local⟩ := is_local,

  set U := is_locally_quotient.Uo hm f_deg VV with U_eq,

  have y_mem_U : y.1 ∈ U,
  { use ⟨y.1, y_mem⟩,
    rw set.mem_preimage,
    exact hom_y_mem_VV, },

  set subset2 : U ⟶ _ := is_locally_quotient.subset2 hm f_deg VV subset1,
  refine ⟨U, y_mem_U, subset2, α' * f^l2, β' * f^l1, m * l1 + l2 * m,
    set_like.graded_monoid.mul_mem α'_mem (set_like.graded_monoid.pow_mem _ f_deg),
    by { convert set_like.graded_monoid.mul_mem β'_mem (set_like.graded_monoid.pow_mem _ f_deg) using 2, rw [smul_eq_mul], ring, }, _⟩,


  rintros ⟨z, z_mem_U⟩,
  have z_mem_bo : z ∈ pbo f,
  { obtain ⟨⟨z, hz⟩, rfl⟩ := z_mem_U,
    rw set.mem_preimage at hz,
    apply z.2, },

  have hom_z_mem_VV : ((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩ ∈ VV,
  { obtain ⟨γ, h1, h2⟩ := z_mem_U,
    have mem1 := γ.2,
    erw set.mem_preimage at mem1,
    exact mem1, },

  specialize is_local ⟨((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z, z_mem_bo⟩), hom_z_mem_VV⟩,
  obtain ⟨not_mem1, eq1⟩ := is_local,

  have not_mem2 : β' * f ^ l1 ∉ z.as_homogeneous_ideal,
  { intro rid,
    rcases z.is_prime.mem_or_mem rid with H1 | H2,
    { apply not_mem1,
      have eq2 : (localization.mk β' ⟨f^l2, ⟨_, rfl⟩⟩ : localization.away f) =
        localization.mk 1 ⟨f^l2, ⟨_, rfl⟩⟩ * localization.mk β' 1,
      { rw [localization.mk_mul, one_mul, mul_one], },
      simp only [eq2],
      erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
      dsimp only,
      convert ideal.mul_mem_left _ _ _,
      apply ideal.subset_span,
      refine ⟨β', H1, rfl⟩, },
    { replace H2 := z.is_prime.mem_of_pow_mem _ H2,
      exact z_mem_bo H2, } },
  refine ⟨not_mem2, _⟩,
  have data_eq : data hm f_deg hh (subset2 ⟨z, z_mem_U⟩) =
    hh.val (subset1 ⟨((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨z, z_mem_bo⟩, hom_z_mem_VV⟩),
  { congr', },
  rw ←data_eq at eq1,

  have z_mem2 : z ∈ (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
        ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop),
  { use z,
    refine ⟨_, rfl⟩,
    erw set.mem_preimage,
    apply (le_of_hom subset1),
    exact hom_z_mem_VV, },

  have data_eq2 : data hm f_deg hh (subset2 ⟨z, z_mem_U⟩) = data hm f_deg hh ⟨z, z_mem2⟩,
  { congr', },
  rw [data_eq2, data.eq_num_div_denom, localization.mk_eq_mk'] at eq1,
  erw is_localization.eq at eq1,

  obtain ⟨⟨⟨_, ⟨L, ⟨C, C_mem⟩, rfl⟩⟩, hC⟩, eq1⟩ := eq1,
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val] at eq1,
  simp only [degree_zero_part.eq, localization.mk_mul] at eq1,
  erw [localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨_, ⟨M, rfl⟩⟩, eq1⟩ := eq1,
  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl, ←pow_add] at eq1,

  unfold bmk,
  rw [homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  unfold num denom,

  set p := degree_zero_part.num (data.num hm f_deg hh ⟨z, z_mem2⟩) with p_eq,
  set q := degree_zero_part.num (data.denom hm f_deg hh ⟨z, z_mem2⟩) with q_eq,
  set ii := degree_zero_part.deg (data.num hm f_deg hh ⟨z, z_mem2⟩) with ii_eq,
  set jj := degree_zero_part.deg (data.denom hm f_deg hh ⟨z, z_mem2⟩) with jj_eq,

  simp only [localization.mk_eq_mk', is_localization.eq],

  have C_not_mem : C ∉ z.as_homogeneous_ideal,
  { intro rid,
    have eq1 : (localization.mk C ⟨f ^ L, ⟨_, rfl⟩⟩ : localization.away f) =
      (localization.mk 1 ⟨f^L, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
      rw [localization.mk_mul, one_mul, mul_one],
    simp only [eq1] at hC,
    apply hC,
    change _ * _ ∈ _,
    rw [set_like.mem_coe],
    convert ideal.mul_mem_left _ _ _,
    apply ideal.subset_span,
    refine ⟨C, rid, rfl⟩ },

  refine ⟨⟨C * f^(L+M), begin
    intro rid,
    rcases z.is_prime.mem_or_mem rid with H1 | H2,
    apply C_not_mem H1,
    replace H2 := z.is_prime.mem_of_pow_mem _ H2,
    apply z_mem_bo,
    exact H2,
  end⟩, _⟩,

  simp only [←subtype.val_eq_coe,
    show ∀ (α β : submonoid.powers f), (α * β).1 = α.1 * β.1, from λ _ _, rfl],

  suffices EQ : p * f^jj * (β' * f^l1) * (C * f^(L+M)) = α' * f^l2 * (q * f^ii) * (C * f^(L + M)),
  convert EQ,
  rw calc p * f^jj * (β' * f^l1) * (C * f^(L+M))
        = p * f^jj * (β' * f^l1) * (C * (f^L * f^M)) : by simp only [pow_add]
    ... = p * β' * C * (f^l1 * f^jj * f^L) * f^M : by ring
    ... = p * β' * C * f^(l1 + jj + L) * f^M : by simp only [pow_add]
    ... = α' * q * C * f ^ (ii + l2 + L) * f ^ M : by rw eq1,

  simp only [pow_add],
  ring,
end

def to_fun.aux (hh : (Spec (A⁰_ f_deg)).presheaf.obj V) : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V :=
⟨bmk hm f_deg V hh, λ y, begin 
  rcases is_locally_quotient hm f_deg V hh y with ⟨VV, mem1, subset1, a, b, degree, a_mem, b_mem, l⟩,
  refine ⟨VV, mem1, subset1, degree, ⟨a, a_mem⟩, ⟨b, b_mem⟩, λ x, _⟩,
  rcases l x with ⟨s_nin, l⟩,
  refine ⟨s_nin, _⟩,
  dsimp only,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],
  erw ← l,
  rw ← homogeneous_localization.ext_iff_val,
  congr' 1
end⟩

def to_fun : (Spec (A⁰_ f_deg)).presheaf.obj V ⟶ ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V :=
{ to_fun := λ hh, to_fun.aux hm f_deg V hh,
  map_one' := begin
    rw subtype.ext_iff_val,
    convert bmk_one hm f_deg V,
  end,
  map_mul' := λ x y, begin
    rw subtype.ext_iff_val,
    convert bmk_mul hm f_deg V x y,
  end,
  map_zero' := begin
    rw subtype.ext_iff_val,
    convert bmk_zero hm f_deg V,
  end,
  map_add' := λ x y, begin
    rw subtype.ext_iff_val,
    convert bmk_add hm f_deg V x y,
  end }

end from_Spec

def from_Spec {f : A} {m : ℕ} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) : 
  (Spec (A⁰_ f_deg)).presheaf ⟶ (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf :=
{ app := λ V, from_Spec.to_fun hm f_deg V,
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    refl,
  end }

namespace from_Spec_to_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens (Spec.T (A⁰_ f_deg)))ᵒᵖ)
variables (hh : ((Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf).obj V)
variables (z : (((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop))

lemma section_congr
  (hh : ((Spec (A⁰_ f_deg)).presheaf).obj V) (x y : unop V) (h1 : x = y)
  (a : _) (b : x.1.as_ideal.prime_compl)
  (h2 : (hh.1 x) = localization.mk a b) : (hh.1 y) = localization.mk a ⟨b.1, begin
    intro rid,
    apply b.2,
    simp only [h1],
    exact rid
  end⟩ :=
begin
  induction h1,
  convert h2,
  rw subtype.ext_iff_val,
end

lemma inv_hom_apply_eq :
  ((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1 = z.1 :=
begin
  change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg _)).1 = z.1,
  rw Proj_iso_Spec_Top_component.from_Spec_to_Spec,
end

lemma pt_eq :
  z = ⟨((Proj_iso_Spec_Top_component hm f_deg).inv ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg _ _⟩)).1, begin
    simpa only [inv_hom_apply_eq hm f_deg V z] using z.2,
  end⟩ :=
begin
  rw [subtype.ext_iff_val, inv_hom_apply_eq],
end

lemma C_not_mem (C : A) (L1 : ℕ) (C_mem : C ∈ 𝒜 (m * L1))
  (hC : (⟨localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩, ⟨L1, ⟨_, C_mem⟩, rfl⟩⟩ : A⁰_ f_deg) ∉ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩).as_ideal) :
  C ∉ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  have eq1 : (localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩ : localization.away f) =
    (localization.mk 1 ⟨f^L1, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk C 1,
    rw [localization.mk_mul, one_mul, mul_one],
  simp only [eq1] at hC,
  apply hC,
  erw Proj_iso_Spec_Top_component.to_Spec.mem_carrier_iff,
  dsimp only,
  convert ideal.mul_mem_left _ _ _,
  apply ideal.subset_span,
  refine ⟨C, rid, rfl⟩,
end 

lemma C_not_mem2
  (C : A) (ι L1 L2 : ℕ) (C_mem : C ∈ 𝒜 (m * L1))
  (hC : (⟨localization.mk C ⟨f ^ L1, ⟨_, rfl⟩⟩, ⟨L1, ⟨_, C_mem⟩, rfl⟩⟩ : A⁰_ f_deg) ∉ 
    ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩).as_ideal)
  (β : A) 
  (β_not_in : β ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1.as_homogeneous_ideal) :
  C * β^m.pred * f^(ι+L1+L2) ∉ z.1.as_homogeneous_ideal :=
begin
  intro rid,
  rcases z.1.is_prime.mem_or_mem rid with H1 | H3,
  rcases z.1.is_prime.mem_or_mem H1 with H1 | H2,
  apply C_not_mem hm f_deg,
  exact hC,
  exact H1,
  replace H2 := z.1.is_prime.mem_of_pow_mem _ H2,
  apply β_not_in,
  have eq1 : (((Proj_iso_Spec_Top_component hm f_deg).inv) ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1 = z.1,
  { change (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 _ _)).1 = z.1,
    rw Proj_iso_Spec_Top_component.from_Spec_to_Spec, },
  erw eq1,
  exact H2,
  replace H3 := z.1.is_prime.mem_of_pow_mem _ H3,
  have mem2 := z.2,
  obtain ⟨⟨a, ha⟩, ha2, ha3⟩ := mem2,
  change a = z.1 at ha3,
  apply ha,
  rw ha3,
  exact H3,
end

include hm
lemma final_eq
  (a α β b C : A) (ι ii jj L1 L2 : ℕ)
  (data_eq2 : α * β ^ m.pred * b * C * f ^ (ii + ι + L1) * f ^ L2 = a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2) :
  a * f ^ jj * β * (C * β ^ m.pred * f ^ (ι + L1 + L2)) = α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2)) :=
begin
  symmetry,
  rw calc α * (b * f ^ ii) * (C * β ^ m.pred * f ^ (ι + L1 + L2))
        = α * β ^ m.pred * b * C * (f^ii * f^(ι + L1 + L2)) : by ring
    ... = α * β ^ m.pred * b * C * (f^ii * (f^ι * f^L1 * f^L2)) : by simp only [pow_add]
    ... = α * β ^ m.pred * b * C * (f ^ ii * f^ι * f^L1) * f ^ L2 : by ring
    ... = α * β ^ m.pred * b * C * (f ^ (ii + ι + L1)) * f ^ L2 : by simp only [pow_add]
    ... = a * β ^ m * C * f ^ (ι + jj + L1) * f ^ L2 : by rw data_eq2
    ... = a * β ^ (m.pred + 1) * C * f ^ (ι + jj + L1) * f ^ L2
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end,
  simp only [pow_add, pow_one],
  ring,
end

section

omit hm
lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec :
  from_Spec.bmk hm f_deg V
    (((to_Spec 𝒜 hm f_deg).app V) hh) z = hh.1 z :=
begin
  unfold from_Spec.bmk,
  rw [homogeneous_localization.ext_iff_val, homogeneous_localization.val_mk'],
  simp only [← subtype.val_eq_coe],

  set hom_z := (Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩ with hom_z_eq,
  have hom_z_mem_V : hom_z ∈ unop V,
  { apply from_Spec.data_prop2 hm f_deg V _, },

  set data := from_Spec.data hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z with data_eq,
  have data_eq1 := data_eq,
  replace data_eq1 : data = to_Spec.fmk hm hh ⟨hom_z, hom_z_mem_V⟩,
  { convert data_eq1, },
  unfold to_Spec.fmk to_Spec.num to_Spec.denom at data_eq1,

  have data_eq2 := from_Spec.data.eq_num_div_denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z,
  rw [←data_eq, data_eq1] at data_eq2,
  set α := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).num with α_eq,
  set β := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom with β_eq,
  set ι := (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).deg with ι_eq,
  have β_not_in : β ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv)
      ((Proj_iso_Spec_Top_component hm f_deg).hom ⟨z.1, from_Spec.data_prop1 hm f_deg V _⟩)).1.as_homogeneous_ideal,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).denom_not_mem, },
  have hartshorne_eq : (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).val
    = localization.mk α ⟨β, β_not_in⟩,
  { exact (hh.1 ⟨((Proj_iso_Spec_Top_component hm f_deg).inv hom_z).1, to_Spec.inv_mem ⟨hom_z, hom_z_mem_V⟩⟩).eq_num_div_denom, },
  
  have eq0 : (hh.1 z).val = localization.mk α ⟨β, begin
    rw inv_hom_apply_eq at β_not_in,
    convert β_not_in,
  end⟩,
  { have := (pt_eq hm f_deg V z),
    convert hartshorne_eq;
    rw pt_eq hm f_deg V z,
    refl,
    ext,
    refl, },
  rw eq0,

  simp only [←α_eq, ←β_eq, ←ι_eq] at data_eq2,
  erw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨⟨_, ⟨L1, ⟨C, C_mem⟩, rfl⟩⟩, hC⟩, data_eq2⟩ := data_eq2,
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val] at data_eq2,
  rw [degree_zero_part.eq, degree_zero_part.eq] at data_eq2,
  set a := degree_zero_part.num (from_Spec.data.num hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with a_eq,
  set b := degree_zero_part.num (from_Spec.data.denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with b_eq,
  set ii := degree_zero_part.deg (from_Spec.data.num hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with ii_eq,
  set jj := degree_zero_part.deg (from_Spec.data.denom hm f_deg (((to_Spec 𝒜 hm f_deg).app V) hh) z) with jj_eq,
  simp only [localization.mk_mul] at data_eq2,
  rw [localization.mk_eq_mk', is_localization.eq] at data_eq2,
  obtain ⟨⟨_, ⟨L2, rfl⟩⟩, data_eq2⟩ := data_eq2,
  simp only [←subtype.val_eq_coe, show ∀ (p q : submonoid.powers f), (p * q).1 = p.1 * q.1, from λ _ _, rfl,
    ←pow_add] at data_eq2,
  unfold from_Spec.num from_Spec.denom,
  dsimp only,
  rw [localization.mk_eq_mk', is_localization.eq],

  refine ⟨⟨C * β^m.pred * f^(ι+L1+L2), by { apply C_not_mem2, exact hC, exact β_not_in }⟩, _⟩,
  { simp only [←subtype.val_eq_coe],
    apply final_eq,
    exact hm,
    exact data_eq2 },
end

end

end from_Spec_to_Spec

namespace to_Spec_from_Spec

variables {𝒜} {m : ℕ} {f : A} (hm : 0 < m) (f_deg : f ∈ 𝒜 m) (V : (opens ((Spec.T (A⁰_ f_deg))))ᵒᵖ)
variables  (hh : ((Spec (A⁰_ f_deg)).presheaf.obj V)) (z : V.unop)

lemma inv_mem :
((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈
  ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop :=
begin
  have mem1 := ((Proj_iso_Spec_Top_component hm f_deg).inv z).2,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z), _, rfl⟩,
  erw set.mem_preimage,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
end

lemma inv_mem_pbo :
    ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 ∈ pbo f :=
begin
  intro rid,
  obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := inv_mem hm f_deg V z,
  change a = ((Proj_iso_Spec_Top_component hm f_deg).inv z).1 at ha3,
  erw ←ha3 at rid,
  apply ha1,
  exact rid,
end

lemma dd_not_mem_z
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl) :
  dd.1 ∉ z.1.as_ideal :=
begin
  have mem1 := dd.2,
  change dd.1 ∉ (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩).as_ideal at mem1,
  convert mem1,
  change z.1 = Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _),
  rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
  refl,
end

lemma eq0
  (dd : (prime_spectrum.as_ideal
    (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (data_eq1 : localization.mk nn dd =
    hh.val ⟨((Proj_iso_Spec_Top_component hm f_deg).hom)
    ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).val, _⟩, begin
      convert z.2,
      change (Proj_iso_Spec_Top_component.to_Spec.to_fun 𝒜 f_deg (Proj_iso_Spec_Top_component.from_Spec.to_fun f_deg hm _)) = z.1,
      rw Proj_iso_Spec_Top_component.to_Spec_from_Spec,
      refl,
    end⟩) :
  (hh.1 z) = localization.mk nn ⟨dd.1, dd_not_mem_z hm f_deg V z dd⟩ :=
begin
  convert from_Spec_to_Spec.section_congr f_deg V hh _ _ _ nn ⟨dd.1, _⟩ _,
  refine ⟨((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨(((Proj_iso_Spec_Top_component hm f_deg).inv) ↑z).val, _⟩, _⟩,
  apply inv_mem_pbo,
  convert z.2,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  rw subtype.ext_iff_val,
  convert Proj_iso_Spec_Top_component.to_Spec_from_Spec _ _ _ _,
  exact dd.2,
  rw ← data_eq1,
  congr' 1,
  rw subtype.ext_iff_val,
end

lemma not_mem1
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉ (((Proj_iso_Spec_Top_component hm f_deg).inv z)).1.as_homogeneous_ideal) :
  (⟨localization.mk ((graded_algebra.proj 𝒜 j) C ^ m) ⟨f ^ j, ⟨j, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem m (submodule.coe_mem _)⟩, rfl⟩⟩ : A⁰_ f_deg) ∈
  (prime_spectrum.as_ideal z.val).prime_compl :=
begin
  intro rid,
  change graded_algebra.proj 𝒜 j C ∉ Proj_iso_Spec_Top_component.from_Spec.carrier _ at hj,
  apply hj,
  intro k,
  by_cases ineq : j = k,
  { rw ←ineq,
    convert rid using 1,
    rw subtype.ext_iff_val,
    dsimp only,
    congr' 1,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_same],
    exact submodule.coe_mem _, },
  { convert submodule.zero_mem _ using 1,
    rw subtype.ext_iff_val,
    dsimp only,
    rw [graded_algebra.proj_apply, direct_sum.decompose_of_mem_ne],
    rw [zero_pow hm, localization.mk_zero],
    refl,
    exact submodule.coe_mem _,
    exact ineq, }
end

lemma eq1
  (hart : homogeneous_localization 𝒜 ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (EQ : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C =
        degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C) :
  hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val * (graded_algebra.proj 𝒜 j) C ^ m *
    f ^ (degree_zero_part.deg nn + hart.deg + j) =
  degree_zero_part.num nn * hart.denom ^ m * (graded_algebra.proj 𝒜 j) C ^ m *
    f ^ (hart.deg + degree_zero_part.deg dd.val + j) :=
begin
  rw calc hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj 𝒜 j) C ^ m * f ^ (degree_zero_part.deg nn + hart.deg + j)
          = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * (graded_algebra.proj 𝒜 j) C ^ (m.pred + 1) * f ^ (degree_zero_part.deg nn + hart.deg + j)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos hm,
          end
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj 𝒜 j) C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * f ^ (degree_zero_part.deg nn + hart.deg + j) : by simp only [pow_add, pow_one]
      ... = hart.num * hart.denom ^ m.pred * degree_zero_part.num dd.val
            * ((graded_algebra.proj 𝒜 j) C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * (f ^ degree_zero_part.deg nn * f ^ hart.deg * f^j) : by simp only [pow_add]
      ... = (hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * graded_algebra.proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * graded_algebra.proj 𝒜 j C ^ m.pred * f ^ hart.deg * f ^ j) : by rw EQ
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m.pred * graded_algebra.proj 𝒜 j C)
            * (hart.denom ^ m.pred * hart.denom) * (f ^ hart.deg * f ^ j) : by ring
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m.pred * graded_algebra.proj 𝒜 j C ^ 1)
            * (hart.denom ^ m.pred * hart.denom ^ 1) * (f ^ hart.deg * f ^ j) : by simp only [pow_one]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ (m.pred + 1))
            * (hart.denom ^ (m.pred + 1)) * (f ^ hart.deg * f ^ j) : by simp only [pow_add]
      ... = (degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val)
            * (graded_algebra.proj 𝒜 j C ^ m)
            * (hart.denom ^ m) * (f ^ hart.deg * f ^ j)
          : begin
            congr';
            apply nat.succ_pred_eq_of_pos hm,
          end,
    simp only [pow_add],
    ring,
end

lemma eq2
  (hart : homogeneous_localization 𝒜 ((Proj_iso_Spec_Top_component hm f_deg).inv z).1.as_homogeneous_ideal.to_ideal)
  (C : A) (j : ℕ) (hj : (graded_algebra.proj 𝒜 j) C ∉
    projective_spectrum.as_homogeneous_ideal (((Proj_iso_Spec_Top_component hm f_deg).inv z)).val)
  (proj_C_ne_zero : graded_algebra.proj 𝒜 j C ≠ 0)
  (dd : (prime_spectrum.as_ideal
   (((Proj_iso_Spec_Top_component hm f_deg).hom) ⟨((Proj_iso_Spec_Top_component hm f_deg).inv z).1, inv_mem_pbo hm f_deg V z⟩)).prime_compl)
  (nn : A⁰_ f_deg)
  (eq1 : hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * C =
    degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * C) :
  hart.num * (degree_zero_part.num dd.val * f ^ degree_zero_part.deg nn) * graded_algebra.proj 𝒜 j C =
  degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom * graded_algebra.proj 𝒜 j C :=
begin
  have mem1 := degree_zero_part.num_mem dd.1,
  have mem2 := degree_zero_part.num_mem nn,
  have eq2 := congr_arg
    (graded_algebra.proj 𝒜 (hart.deg + m * degree_zero_part.deg dd.1 + m * degree_zero_part.deg nn + j)) eq1,
  rw graded_algebra.proj_hom_mul at eq2,
  rw graded_algebra.proj_hom_mul at eq2,
  exact eq2,

  rw show degree_zero_part.num nn * f ^ degree_zero_part.deg dd.val * hart.denom =
    hart.denom * f ^ degree_zero_part.deg dd.1 * degree_zero_part.num nn, by ring,
  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply hart.denom_mem,
  rw nat.mul_comm,
  apply set_like.graded_monoid.pow_mem _ f_deg,
  exact mem2,
  exact proj_C_ne_zero,

  rw ←mul_assoc,
  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply hart.num_mem,
  exact mem1,
  rw nat.mul_comm,
  apply set_like.graded_monoid.pow_mem _ f_deg,
  exact proj_C_ne_zero,
end

lemma _root_.algebraic_geometry.Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (V hh z) :
  to_Spec.fmk hm (((from_Spec 𝒜 hm f_deg).app V) hh) z =
  hh.val z :=
begin
  classical,

  set b_hh := ((from_Spec 𝒜 hm f_deg).app V hh) with b_hh_eq,
  unfold to_Spec.fmk to_Spec.num to_Spec.denom,
  set inv_z := ((Proj_iso_Spec_Top_component hm f_deg).inv z) with inv_z_eq,
  have inv_z_mem : inv_z.1 ∈
    ((@opens.open_embedding Proj.T (pbo f)).is_open_map.functor.op.obj
    ((opens.map (Proj_iso_Spec_Top_component hm f_deg).hom).op.obj V)).unop,
  { apply to_Spec_from_Spec.inv_mem, },

  have inv_z_mem_bo : inv_z.1 ∈ projective_spectrum.basic_open 𝒜 f,
  { apply to_Spec_from_Spec.inv_mem_pbo, },

  set hart := b_hh.1 ⟨inv_z.1, inv_z_mem⟩ with hart_eq,
  rw homogeneous_localization.ext_iff_val at hart_eq,
  have hart_eq1 := hart.eq_num_div_denom,
  rw hart_eq at hart_eq1,

  rw b_hh_eq at hart_eq,
  replace hart_eq : hart.val = (from_Spec.bmk hm f_deg V hh ⟨inv_z.val, inv_z_mem⟩).val,
  { convert hart_eq },
  unfold from_Spec.bmk at hart_eq,
  rw [homogeneous_localization.val_mk'] at hart_eq,
  simp only [← subtype.val_eq_coe] at hart_eq,
  unfold from_Spec.num from_Spec.denom at hart_eq,

  set data := from_Spec.data hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with data_eq,
  have data_eq1 := data_eq,
  unfold from_Spec.data at data_eq1,
  erw from_Spec.data.eq_num_div_denom at data_eq,
  erw data_eq at data_eq1,
  set nn := from_Spec.data.num hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with nn_eq,
  set dd := from_Spec.data.denom hm f_deg hh ⟨inv_z.val, inv_z_mem⟩ with dd_eq,
  dsimp only at hart_eq,

  rw hart.eq_num_div_denom at hart_eq,
  rw [localization.mk_eq_mk', is_localization.eq] at hart_eq,
  obtain ⟨⟨C, hC⟩, eq1⟩ := hart_eq,
  simp only [←subtype.val_eq_coe] at eq1,
  have hC2 : ∃ j : ℕ, graded_algebra.proj 𝒜 j C ∉ inv_z.1.as_homogeneous_ideal,
  { by_contra rid,
    rw not_exists at rid,
    apply hC,
    rw ←direct_sum.sum_support_decompose 𝒜 C,
    apply ideal.sum_mem inv_z.1.as_homogeneous_ideal.1,
    intros j hj,
    specialize rid j,
    rw not_not at rid,
    exact rid, },
  obtain ⟨j, hj⟩ := hC2,

  have proj_C_ne_zero : graded_algebra.proj 𝒜 j C ≠ 0,
  { intro rid,
    rw rid at hj,
    apply hj,
    exact submodule.zero_mem _, },

  have dd_not_mem_z : dd ∉ z.val.as_ideal,
  { apply to_Spec_from_Spec.dd_not_mem_z, },

  have eq0 : (hh.1 z) = localization.mk nn ⟨dd, dd_not_mem_z⟩,
  { convert to_Spec_from_Spec.eq0 hm f_deg _ hh z ⟨dd, _⟩ nn data_eq1, },
  rw [eq0, localization.mk_eq_mk', is_localization.eq],
  simp only [←subtype.val_eq_coe, subtype.ext_iff_val, degree_zero_part.mul_val],
  rw [degree_zero_part.eq, degree_zero_part.eq, localization.mk_mul, localization.mk_mul],

  refine ⟨⟨⟨localization.mk ((graded_algebra.proj 𝒜 j C)^m) ⟨f^j, ⟨j, rfl⟩⟩,
    ⟨j, ⟨(graded_algebra.proj 𝒜 j C)^m, set_like.graded_monoid.pow_mem _ (submodule.coe_mem _)⟩, rfl⟩⟩,
    to_Spec_from_Spec.not_mem1 hm f_deg V z C j hj⟩, _⟩,
  { rw [localization.mk_mul, localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
    use 1,
    simp only [←subtype.val_eq_coe,
      show ∀ (p q : submonoid.powers f), (p * q).1 = p.1 * q.1, from λ _ _, rfl, ←pow_add,
      show (1 : submonoid.powers f).1 = 1, from rfl, mul_one, one_mul],
    apply to_Spec_from_Spec.eq1,
    exact hj,
    apply to_Spec_from_Spec.eq2;
    assumption, }
end

end to_Spec_from_Spec

end Proj_iso_Spec_Sheaf_component

def Sheaf_component {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj_iso_Spec_Top_component hm f_deg).hom _* (Proj| (pbo f)).presheaf ≅ (Spec (A⁰_ f_deg)).presheaf :=
{ hom := Proj_iso_Spec_Sheaf_component.to_Spec 𝒜 hm f_deg,
  inv := Proj_iso_Spec_Sheaf_component.from_Spec 𝒜 hm f_deg,
  hom_inv_id' := begin
    ext1,
    ext1 V,
    ext1 hh,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply, subtype.ext_iff_val],
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.from_Spec_to_Spec,
  end,
  inv_hom_id' := begin
    ext1, ext1 V, ext1 hh,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply],
    rw subtype.ext_iff_val,
    ext1 z,
    apply Proj_iso_Spec_Sheaf_component.to_Spec_from_Spec,
  end }

def SheafedSpace.iso_of_PresheafedSpace_iso 
  {C : Type*} [category C] [limits.has_products C] 
  (X Y : @@SheafedSpace C _ (by assumption : limits.has_products C)) (H : X.to_PresheafedSpace ≅ Y.to_PresheafedSpace) : X ≅ Y :=
 { hom := H.hom,
   inv := H.inv,
   hom_inv_id' := H.hom_inv_id',
   inv_hom_id' := H.inv_hom_id' }

def iso {m : ℕ} {f : A} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
  (Proj| (pbo f)) ≅ Spec (A⁰_ f_deg) :=
LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_PresheafedSpace_iso _ _ $ 
@PresheafedSpace.iso_of_components _ _ 
(Proj| (pbo f)).to_PresheafedSpace 
(Spec (A⁰_ f_deg)).to_PresheafedSpace 
(Proj_iso_Spec_Top_component hm f_deg) (Sheaf_component 𝒜 f_deg hm)

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
    refine ⟨⟨pbo f, mem⟩, ⟨A⁰_ f_deg⟩, ⟨iso 𝒜 f_deg hn⟩⟩,
  end,
  ..Proj }

end algebraic_geometry
