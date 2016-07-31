import algebra.order_bigops
open nat

namespace finset

definition fresh [reducible] (x : finset ℕ) : ℕ := succ (Max₀ x)

theorem fresh_not_mem (x : finset ℕ) : fresh x ∉ x :=
  suppose H : succ (Max₀ x) ∈ x,
  have succ (Max₀ x) ≤ Max₀ x, from le_Max₀ H,
  show false, from not_succ_le_self this

end finset
