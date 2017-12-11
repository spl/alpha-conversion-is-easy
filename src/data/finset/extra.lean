/-

This file contains extra definitions and theorems for `finset`.

-/

import data.finset

namespace finset ---------------------------------------------------------------

variables {A : Type} [decidable_eq A] {a b : A} {s : finset A}

-- Given `s : finset A`, `a ∈ s`, and `b ∉ s`, show that `a ≠ b`.
theorem ne_of_mem_of_not_mem : a ∈ s → b ∉ s → a ≠ b :=
  λ a_in_s b_not_in_s,
  ne_of_mem_erase (@@eq.substr _ (erase_insert b_not_in_s) a_in_s)

end /- namespace -/ finset -----------------------------------------------------
