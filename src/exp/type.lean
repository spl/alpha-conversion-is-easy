/-

This file contains the `exp` inductive data type.

-/

import name

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

/-
`exp` is an inductive data type representing a lambda calculus expression
language. The type is indexed by a finite set of variables that are free in the
given expression.
-/

inductive exp : finset V → Type
  | var : Π {X : finset V},         ν∈ X             → exp X  -- variable
  | app : Π {X : finset V},         exp X → exp X    → exp X  -- application
  | lam : Π {X : finset V} {a : V}, exp (insert a X) → exp X  -- lambda abstraction

end alpha
