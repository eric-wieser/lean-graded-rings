import ring_theory.localization.away

import cicm2022.internal.graded_ring

noncomputable theory

namespace algebraic_geometry

open_locale big_operators pointwise
open set_like.graded_monoid localization finset (hiding mk_zero)

variables {R A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜]

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

end algebraic_geometry
