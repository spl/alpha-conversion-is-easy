/-

This file contains declarations related to `nrel` inversion or symmetry.

-/

import .id

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X Y : finset V}
variables {R : X ×ν Y}
variables {x x₁ x₂ : ν∈ X} {y : ν∈ Y}

namespace alpha

namespace nrel

-- `inv R` inverts the order of the relation `R`.
@[reducible]
def inv : X ×ν Y → Y ×ν X :=
  -- An alternative def for this is `function.swap`; however, that does
  -- not unfold as easily as the explicit lambda.
  λ R y x, R x y

-- Notation for `inv`.
postfix ⁻¹ := inv

@[reducible]
protected
theorem symm : ⟪x, y⟫ ∈ν R → ⟪y, x⟫ ∈ν R⁻¹ :=
  λ m, m

end nrel

end alpha
