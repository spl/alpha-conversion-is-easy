/-

This file contains the `aeq` data type.

We put the data type in its own file because it takes a long time to compile and
we want Lean to cache the results.

-/

import exp
import vrel

namespace alpha ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

/-
`aeq R e₁ e₂` is an inductive data type that relates `e₁ : exp X` and `e₂ : exp
Y` via their free variables with `R : X ×ν Y`.
-/

inductive aeq : Π {X Y : vs V}, X ×ν Y → exp X → exp Y → Prop
  | var : Π {X Y : vs V} {R : X ×ν Y}           {x : ν∈ X}              {y : ν∈ Y},              ⟪x, y⟫ ∈ν R →               aeq R (exp.var x)     (exp.var y)
  | app : Π {X Y : vs V} {R : X ×ν Y}           {fX eX : exp X}         {fY eY : exp Y},         aeq R fX fY → aeq R eX eY → aeq R (exp.app fX eX) (exp.app fY eY)
  | lam : Π {X Y : vs V} {R : X ×ν Y} {a b : V} {eX : exp (insert a X)} {eY : exp (insert b Y)}, aeq (R ⩁ (a, b)) eX eY →    aeq R (exp.lam eX)    (exp.lam eY)

-- Notation for `aeq`.
notation e₁ ` ≡α⟨`:50 R `⟩ ` e₂:50 := aeq R e₁ e₂

-- An abbreviation for `aeq` with `vrel.id`.
@[reducible]
def aeq.identity (X : vs V) : exp X → exp X → Prop :=
  aeq (vrel.id X)

-- Notation for `aeq.identity`. We leave the `vset` implicit here because it
-- should be inferred using type class elaboration.
infix ` ≡α `:50 := aeq.identity _

end /- namespace -/ alpha ------------------------------------------------------
