import algebra.free_monoid
import data.set.pointwise

import cicm2022.graded_monoid
/-!
This file contains an examples from §2.2 of the corresponding paper.
-/

open_locale pointwise

instance set.set_like {α : Type*} : set_like (set α) α :=
{ coe := id,
  coe_injective' := function.injective_id }

instance free_monoid.graded_monoid {α : Type*} :
  set_like.graded_monoid (λ i : ℕ, (set.range (free_monoid.of : α → free_monoid α)) ^ i) :=
{ one_mem := by rw [pow_zero, set.mem_one],
  mul_mem := λ i j x y hx hy, by { rw pow_add, exact set.mul_mem_mul hx hy} }