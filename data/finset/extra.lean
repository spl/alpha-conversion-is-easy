/-

This file contains extra definitions and theorems for `finset.

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

theorem eq_of_mem_insert (a_mem_s : a ∈ s) (a_ne_b : a ≠ b)
: mem_of_mem_insert_of_ne (mem_insert_of_mem b a_mem_s) a_ne_b = a_mem_s :=

  by unfold [mem_of_mem_insert_of_ne, mem_insert_of_mem]

end finset -- namespace --------------------------------------------------------
