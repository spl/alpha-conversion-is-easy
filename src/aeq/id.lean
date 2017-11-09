/-

This file contains declarations related to `aeq` identity or reflexivity.

-/

import .properties

namespace acie ----------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

-- Identity `aeq` with an implicit `vset`.
@[inline, reducible]
def aeq.id {X : vs V} : exp X → exp X → Prop :=
  aeq (vrel.id X)

-- Notation for `aeq.id`.
infix ` ≡α `:50 := aeq.id

namespace id -------------------------------------------------------------------
-- Paper: Corollary 3

-- Reflexivity of `aeq.id`
protected
theorem refl (X : vs V) : reflexive (aeq (vrel.id X)) :=
  aeq.refl

-- Symmetry of `aeq.id`
protected
theorem symm (X : vs V) : symmetric (aeq (vrel.id X)) :=
  λ e₁ e₂ a,
  map.simple (λ x₁ x₂, vrel.inv.of_id) (aeq.symm a)

-- Transitivity of `aeq.id`
protected
theorem trans (X : vs V) : transitive (aeq (vrel.id X)) :=
  λ e₁ e₂ e₃ a₁ a₂,
  map.simple (λ x₁ x₂, vrel.id.of_comp) (aeq.trans a₁ a₂)

end /- namespace -/ id ---------------------------------------------------------

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie ------------------------------------------------------
