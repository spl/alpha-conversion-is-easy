/-

This file defines the `decidable_eq` instance of the `has_mem` class.

-/

universes u v
variables {α : Type u} {γ : Type v}

instance has_mem.decidable_eq (a : α) (b : γ) [has_mem α γ]
: decidable_eq (has_mem.mem a b) :=
  λ p₁ p₂, decidable.is_true (proof_irrel p₁ p₂)
