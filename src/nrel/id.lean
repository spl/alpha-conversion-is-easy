/-

This file contains declarations related to `nrel` identity or reflexivity.

-/

import .type

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X : finset V}

namespace alpha

namespace nrel

-- `id X` creates an identity variable relation from the single finite set `X`.
@[reducible]
protected
definition id (X : finset V) : X ×ν X :=
  eq

-- Constructor
@[reducible]
protected
theorem refl : ∀ (x : ν∈ X), ⟪x, x⟫ ∈ν nrel.id X :=
  eq.refl

end nrel

end alpha
