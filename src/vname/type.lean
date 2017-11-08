/-

This file contains the `vname` type, the type of variable names in a variable
set, and other related type definitions.

-/

import vset

namespace alpha

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets

/-
A `vname X` is a variable name (e.g. `a : V`) paired with the status of its
membership in the variable name set `X` (e.g. `a ∈ X`).

The underlying type is `psigma`, so we can use the anonymous constructor
notation `x = ⟨a, pa⟩` to refer to a `x : vname X` with the variable, `a : V`
(or `x.1`), and its proof of membership, `pa : P a X` (or `x.2`).
-/

@[reducible]
def vname (P : Prop → Prop) (X : vs V) : Type :=
  Σ' a : V, P (a ∈ X)

namespace vname

/-
A `vname.id X` is a variable name set member. Its variable name is an element of
the variable name set `X`.
-/
@[reducible]
protected
def id : vs V → Type :=
  vname id

/-
A `vname.not X` is a variable set non-member. Its variable name is *not* an
element of the variable name set `X`.
-/
@[reducible]
protected
def not : vs V → Type :=
  vname not

-- Notation for `vname.id` and `vname.not`.
prefix `ν∈ `:40 := vname.id   -- \nu\in
prefix `ν∉ `:40 := vname.not  -- \nu\notin

-- A function from an `vname.id` to an `vname.id`.
@[reducible]
protected
def id.fun (X Y : vs V) : Type :=
  ν∈ X → ν∈ Y

-- Notation for `vname.id.fun`.
infixr `→ν`:25 := vname.id.fun

end vname

end alpha
