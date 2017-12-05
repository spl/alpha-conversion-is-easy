/-

This file contains declarations related to `vrel` identity or reflexivity.

-/

import .type

namespace acie -----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

-- `id X` creates an identity variable relation from the single finite set `X`.
@[reducible]
protected
def id (X : vs V) : X ×ν X :=
  eq

-- Constructor
@[reducible]
protected
theorem refl : ∀ (x : ν∈ X), ⟪x, x⟫ ∈ν vrel.id X :=
  eq.refl

instance id.decidable (x₁ x₂ : ν∈ X) : decidable (⟪x₁, x₂⟫ ∈ν vrel.id X) :=
  by apply_instance

end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
