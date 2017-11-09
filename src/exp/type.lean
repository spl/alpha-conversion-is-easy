/-

This file contains the `exp` inductive data type.

-/

import vname

namespace alpha ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

/-
`exp` is an inductive data type representing a lambda calculus expression
language. The type is indexed by a finite set of variables that are free in the
given expression.
-/

inductive exp : vs V → Type
  | var : Π {X : vs V},         ν∈ X             → exp X  -- variable
  | app : Π {X : vs V},         exp X → exp X    → exp X  -- application
  | lam : Π {X : vs V} {a : V}, exp (insert a X) → exp X  -- lambda abstraction

end /- namespace -/ alpha ------------------------------------------------------
