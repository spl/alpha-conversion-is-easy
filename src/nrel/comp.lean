/-

This file contains declarations related to `nrel` composition or transitivity.

-/

import .id

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X Y Z : finset V}

namespace alpha

namespace nrel

-- `comp R S` combines the relations `R` and `S` to create a new relation
-- that is the composition of their underlying finite sets.
@[reducible]
definition comp (R : X ×ν Y) (S : Y ×ν Z) : X ×ν Z :=
  λ x z, ∃ y, R x y ∧ S y z

-- Notation for `comp`.
-- Source: http://www.fileformat.info/info/unicode/char/2a3e/index.htm
infixr ` ⨾ `:60 := comp

variables {R : X ×ν Y} {S : Y ×ν Z}
variables {x : ν∈ X} {y : ν∈ Y} {z : ν∈ Z}

-- Constructor
@[reducible]
protected
theorem trans : ⟪x, y⟫ ∈ν R → ⟪y, z⟫ ∈ν S → ⟪x, z⟫ ∈ν R ⨾ S :=
  λ x_R_y y_S_z, exists.intro y $ and.intro x_R_y y_S_z

end nrel

end alpha
