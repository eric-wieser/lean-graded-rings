/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

From: https://github.com/leanprover-community/mathlib/pull/10255
-/
import cicm2022.external.graded_monoid
import data.fin.vec_notation

/-! # Tuples `fin na → α` form a graded ring under append -/

namespace fin

variables {α : Sort*} {α' : Type*} {na nb nc : ℕ}

/-- Append `b` to `a`.

Note that for brevity, in the paper we just write `fin.add_cases a b`; in actuality, we have to
fight against higher-order unification in the elaborator. -/
def append' (a : fin na → α) (b : fin nb → α) : fin (na + nb) → α :=
@fin.add_cases _ _ (λ _, α) a b

/-- Repeat `a` `n` times. -/
def repeat (a : fin na → α) (n : ℕ) : fin (n * na) → α
| i := a ⟨i % na, nat.mod_lt _ $ pos_of_mul_pos_left ((nat.zero_le i).trans_lt i.is_lt) n.zero_le⟩

@[simp] lemma append'_apply_left {α} {na nb} (a : fin na → α) (b : fin nb → α) (i : fin na) :
  append' a b (fin.cast_add _ i) = a i :=
fin.add_cases_left _ _ _

@[simp] def append'_apply_right {α} {na nb} (a : fin na → α) (b : fin nb → α) (j : fin nb) :
  append' a b (nat_add _ j) = b j :=
fin.add_cases_right _ _ _

lemma append'_cases {na nb} {P : fin (na + nb) → Prop}
  (hl : ∀ l : fin na, P (fin.cast_add _ l))
  (hr : ∀ r : fin nb, P (nat_add _ r)) : ∀ i, P i :=
fin.add_cases hl hr

lemma append'_elim0 (a : fin na → α) : append' a fin.elim0 = a ∘ fin.cast (add_zero _) :=
begin
  ext i,
  apply append'_cases (λ l, _) fin.elim0 i,
  rw [append'_apply_left],
  refine congr_arg a (fin.ext _),
  simp,
end

lemma elim0_append' (b : fin nb → α) : append' (fin.elim0 : _ → α) b = b ∘ fin.cast (zero_add _) :=
begin
  ext i,
  apply append'_cases fin.elim0 (λ r, _) i,
  rw [append'_apply_right],
  refine congr_arg b (fin.ext _),
  simp,
end

lemma cast_add_cast_add {m n p : ℕ} (i : fin m) :
  cast_add p (cast_add n i) = cast (add_assoc _ _ _).symm (cast_add (n + p) i) :=
ext rfl

lemma cast_add_nat_add {m n p : ℕ} (i : fin n) :
  cast_add p (nat_add m i) = cast (add_assoc _ _ _).symm (nat_add m (cast_add p i)) :=
ext rfl

lemma nat_add_nat_add {m n p : ℕ} (i : fin p) :
  nat_add (m + n) i = cast (add_assoc _ _ _).symm (nat_add m (nat_add n i)) :=
ext $ add_assoc _ _ _

lemma append'_assoc (a : fin na → α) (b : fin nb → α) (c : fin nc → α) :
  append' (append' a b) c = append' a (append' b c) ∘ fin.cast (add_assoc _ _ _) :=
begin
  ext i,
  rw function.comp_apply,
  apply append'_cases (λ l, _) (λ r, _) i,
  { rw append'_apply_left,
    apply append'_cases (λ ll, _) (λ lr, _) l,
    { rw append'_apply_left,
      simp [cast_add_cast_add] },
    { rw append'_apply_right,
      simp [cast_add_nat_add], }, },
  { rw [append'_apply_right],
    simp [nat_add_nat_add] },
end

@[simp] lemma repeat_zero (a : fin na → α) : repeat a 0 = fin.elim0 ∘ cast (zero_mul _) :=
begin
  ext,
  rw zero_mul at x,
  exact x.elim0,
end

@[simp] lemma repeat_succ (a : fin na → α) (n : ℕ) :
  repeat a n.succ = append' a (repeat a n) ∘ cast ((nat.succ_mul _ _).trans (add_comm _ _)) :=
have n.succ * na = na + n * na := by rw [nat.succ_mul, add_comm],
begin
  apply funext,
  rw (fin.cast this.symm).surjective.forall,
  refine fin.add_cases (λ l, _) (λ r, _),
  { simp[repeat, nat.mod_eq_of_lt l.is_lt], },
  { simp[repeat] }
end

/-- To show two sigma pairs of tuples agree, we have to show the second elements are related via
`fin.cast`. -/
lemma sigma_eq_of_eq_comp_cast :
  ∀ {a b : Σ ii, fin ii → α'} (h : a.fst = b.fst), a.snd = b.snd ∘ fin.cast h → a = b
| ⟨ai, a⟩ ⟨bi, b⟩ hi h :=
begin
  simp only at hi,
  subst hi,
  simpa using h,
end

instance tuple.gmonoid {α : Type*} : graded_monoid.gmonoid (λ n, fin n → α) :=
{ mul := λ i j, fin.append',
  one := fin.elim0,
  one_mul := λ b, sigma_eq_of_eq_comp_cast _ (elim0_append' _),
  mul_one := λ a, sigma_eq_of_eq_comp_cast _ (append'_elim0 _),
  mul_assoc := λ a b c, sigma_eq_of_eq_comp_cast _ $ (append'_assoc a.2 b.2 c.2).trans rfl,
  -- note that these three fields are optional, they can be commented out without issue
  gnpow := λ n i a, repeat a n,
  gnpow_zero' := λ a, sigma_eq_of_eq_comp_cast _ (repeat_zero _),
  gnpow_succ' := λ a n, sigma_eq_of_eq_comp_cast _ (repeat_succ _ _)
  }

end fin
