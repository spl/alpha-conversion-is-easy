/-

This file contains the `nrel` type, a binary relation on finite sets of
variable names.

-/

import name

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

/-
`nrel` is the type of a binary relation on finite sets of variable names. It is
defined by a function on two variable names in their respective finite sets `X`
and `Y`.
-/

definition nrel (X Y : finset V) : Type :=
  ν∈ X → ν∈ Y → Prop

-- Notation for `nrel`.
infixl ` × ` := nrel
