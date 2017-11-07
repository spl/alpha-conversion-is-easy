/-

This file contains the `nrel` type, a binary relation on finite sets of
variable names.

-/

import name

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

/-
`nrel` is the type of a binary relation on finite sets of variable names. It is
defined by a function on two variable names in their respective finite sets `X`
and `Y`.
-/

@[reducible]
definition nrel (X Y : finset V) : Type :=
  ν∈ X → ν∈ Y → Prop

-- Notation for `nrel`.
infixl ` ×ν `:35 := nrel

-- Notation for membership of an `nrel`.
notation `⟪` x `, ` y `⟫` ` ∈ν ` R:50 := R x y

variables {X Y : finset V}

-- Lift a function on finite name sets to a `nrel`
@[reducible]
protected
definition nrel.lift (F : X ν⇒ Y) : X ×ν Y :=
  λ x y, (F x).1 = y.1

end alpha -- namespace
