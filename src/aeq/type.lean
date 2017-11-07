/-

This file contains the `aeq` data type.

We put the data type in its own file because it takes a long time to compile and
we want Lean to cache the results.

-/

import exp
import nrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X : finset V}

namespace alpha

/-
`aeq R e₁ e₂` is an inductive data type that relates `e₁ : exp X` and `e₂ : exp
Y` via their free variables with `R : X ×ν Y`.
-/

inductive aeq : Π {X Y : finset V}, X ×ν Y → exp X → exp Y → Prop
  | var : Π {X Y : finset V} {R : X ×ν Y}           {x : ν∈ X}              {y : ν∈ Y},              ⟪x, y⟫ ∈ν R →               aeq R (exp.var x)     (exp.var y)
  | app : Π {X Y : finset V} {R : X ×ν Y}           {fX eX : exp X}         {fY eY : exp Y},         aeq R fX fY → aeq R eX eY → aeq R (exp.app fX eX) (exp.app fY eY)
  | lam : Π {X Y : finset V} {R : X ×ν Y} {a b : V} {eX : exp (insert a X)} {eY : exp (insert b Y)}, aeq (R ⩁ (a, b)) eX eY →    aeq R (exp.lam eX)    (exp.lam eY)

-- Notation for `aeq`.
notation e₁ ` ≡α⟨`:50 R `⟩ ` e₂:50 := aeq R e₁ e₂

-- An abbreviation for `aeq` with `nrel.id`.
@[reducible]
definition aeq.identity (X : finset V) : exp X → exp X → Prop :=
  aeq (nrel.id X)

-- Notation for `aeq.identity`. We leave the `finset` implicit here because it
-- should be inferred using type class elaboration.
infix ` ≡α `:50 := aeq.identity _

end alpha
