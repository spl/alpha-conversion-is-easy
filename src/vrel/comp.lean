/-

This file contains declarations related to `vrel` composition or transitivity.

-/

import .id

namespace acie -----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y Z : vs V} -- Variable name sets
variables {R : X ×ν Y} {S : Y ×ν Z} -- Variable name set relations
variables {x : ν∈ X} {y : ν∈ Y} {z : ν∈ Z} -- Variable name set members

-- `comp R S` combines the relations `R` and `S` to create a new relation
-- that is the composition of their underlying finite sets.
@[reducible]
def comp (R : X ×ν Y) (S : Y ×ν Z) : X ×ν Z :=
  λ x z, ∃ y, ⟪x, y⟫ ∈ν R ∧ ⟪y, z⟫ ∈ν S

-- Notation for `comp`.
-- Source: http://www.fileformat.info/info/unicode/char/2a3e/index.htm
infixr ` ⨾ `:60 := comp

-- Constructor
@[reducible]
protected
theorem trans : ⟪x, y⟫ ∈ν R → ⟪y, z⟫ ∈ν S → ⟪x, z⟫ ∈ν R ⨾ S :=
  λ x_R_y y_S_z, exists.intro y $ and.intro x_R_y y_S_z

end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
