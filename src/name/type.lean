/-

This file contains the `name` type, the type of variable names in a finite set,
and other related type definitions.

-/

import data.finset

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

/-
`name X` is a pair of a variable name and its membership status w.r.t. to the
finite set `X`.

Since the underlying type is `sigma`, we use the notation `x = ⟨a, pa⟩` to refer
to a `name X` with the variable, `a : V` (or `x.1`), and its proof of
membership, `pa : M a X` (or `x.2`).
-/

@[reducible]
definition name (X : finset V) (M : V → finset V → Prop) : Type :=
  Σ' a : V, M a X

-- A `name` *i*n the finite set `X`.
@[reducible]
definition iname (X : finset V) : Type :=
  name X finset.mem

-- A `name` *o*ut of the finite set `X`.
@[reducible]
definition oname (X : finset V) : Type :=
  name X (λ a X, ¬ finset.mem a X)

-- Notation for `iname` and `oname`.
prefix `ν∈ `:40 := iname  -- \nu\in
prefix `ν∉ `:40 := oname  -- \nu\notin

-- A function from an `iname` to an `iname`.
@[reducible]
definition iname_fun (X Y : finset V) : Type :=
  ν∈ X → ν∈ Y

-- Notation for `iname_fun`.
infixr `ν⇒`:25 := iname_fun

end alpha
