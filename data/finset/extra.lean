/-

This file contains extra definitions and theorems for `finset`.

-/

import data.finset

open [notation] eq.ops
open [notation] function

variables {A : Type} [decidable_eq A]

namespace finset -- ============================================================

variables {a b : A} {s : finset A}

-- Given `s : finset A`, `a ∈ s`, and `b ∉ s`, show that `a ≠ b`.
theorem ne_of_mem_of_not_mem : a ∈ s → b ∉ s → a ≠ b :=
  λ a nb, ne_of_mem_erase $ (erase_insert nb)⁻¹ ▸ a

theorem eq_of_mem_insert_of_ne (a_mem_s : a ∈ s) (a_ne_b : a ≠ b)
: mem_of_mem_insert_of_ne (mem_insert_of_mem b a_mem_s) a_ne_b = a_mem_s :=
  rfl

theorem eq_of_mem_of_subset_of_mem₁ (b_mem_s : b ∈ s)
: mem_of_subset_of_mem (subset_insert s a) b_mem_s = mem_insert_of_mem a b_mem_s :=
  rfl

theorem eq_of_mem_of_subset_of_mem₂ (b_ne_a : b ≠ a) (b_mem_insert : b ∈ '{a} ∪ s)
: mem_of_subset_of_mem (subset_insert s a) (mem_of_mem_insert_of_ne b_mem_insert b_ne_a)
= b_mem_insert :=
  rfl

end finset -- namespace --------------------------------------------------------
