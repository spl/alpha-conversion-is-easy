/-

This file contains extra definitions and theorems for `finset`.

-/

import data.finset

variables {A : Type} [decidable_eq A]

namespace finset -- ============================================================

variables {a b : A} {s : finset A}

-- Given `s : finset A`, `a ∈ s`, and `b ∉ s`, show that `a ≠ b`.
theorem ne_of_mem_of_not_mem : a ∈ s → b ∉ s → a ≠ b :=
  λ a_in_s b_not_in_s,
  ne_of_mem_erase (@@eq.substr _ (erase_insert b_not_in_s) a_in_s)

theorem eq_of_mem_insert_of_ne (a_in_s : a ∈ s) (a_ne_b : a ≠ b)
: mem_of_mem_insert_of_ne (mem_insert_of_mem a_in_s) a_ne_b = a_in_s :=
  rfl

theorem eq_of_mem_of_subset_of_mem₁ (b_in_s : b ∈ s)
: mem_of_subset_of_mem subset_insert b_in_s = @mem_insert_of_mem _ _ _ _ a b_in_s :=
  rfl

theorem eq_of_mem_of_subset_of_mem₂ (b_ne_a : b ≠ a) (b_in_insert_a_s : b ∈ insert a s)
: mem_of_subset_of_mem subset_insert (mem_of_mem_insert_of_ne b_in_insert_a_s b_ne_a) = b_in_insert_a_s :=
  rfl

end finset -- namespace --------------------------------------------------------
