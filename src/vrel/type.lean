/-

This file contains the `vrel` type, a binary relation on finite sets of
variable names.

-/

import vname

namespace acie ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- `vrel` is the type of a binary relation on variable name sets.
@[reducible]
def vrel (X Y : vs V) : Type :=
  ν∈ X → ν∈ Y → Prop

-- Notation for `vrel`.
infixl ` ×ν `:35 := vrel

-- Notation for membership of an `vrel`.
notation `⟪` x `, ` y `⟫` ` ∈ν ` R:50 := R x y

-- Lift a function on finite name sets to a `vrel`
@[reducible]
protected
def vrel.lift (F : X →ν Y) : X ×ν Y :=
  λ x y, (F x).1 = y.1

end /- namespace -/ acie ------------------------------------------------------
