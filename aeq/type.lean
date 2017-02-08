/-

This file contains the `aeq` data type.

We put the data type in its own file because it takes a long time to compile and
we want Lean to cache the results.

-/

import exp
import vrel

open [notation] finset
open [notation] vrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

/-
`aeq R e₁ e₂` is an inductive data type that relates `e₁ : exp X` and `e₂ : exp
Y` via their free variables with `R : vrel X`.
-/

inductive aeq : Π {X Y : finset V}, vrel X Y → exp X → exp Y → Prop :=
  | var : Π {X Y : finset V} {R : vrel X Y}           {x : ν∈ X}            {y : ν∈ Y},            ⟪x, y, R⟫ →                     aeq R (exp.var x)     (exp.var y)
  | app : Π {X Y : finset V} {R : vrel X Y}           {fX eX : exp X}       {fY eY : exp Y},       aeq R fX fY → aeq R eX eY →     aeq R (exp.app fX eX) (exp.app fY eY)
  | lam : Π {X Y : finset V} {R : vrel X Y} {a b : V} {eX : exp ('{a} ∪ X)} {eY : exp ('{b} ∪ Y)}, aeq (vrel.update a b R) eX eY → aeq R (exp.lam eX)    (exp.lam eY)
