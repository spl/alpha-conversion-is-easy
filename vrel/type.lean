/-

This file contains the `vrel` type, a binary relation on finite sets of
variables.

-/

import var

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

/-
`vrel` is type of a binary relation on the finite sets of variable names, `X`
and `Y`. It is defined by a function on two variable names, `x` and `y`, and
their membership in the respective sets.
-/

definition vrel (X Y : finset V) : Type :=
  ν∈ X → ν∈ Y → Prop
