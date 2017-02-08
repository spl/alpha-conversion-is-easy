/-

This files defines the `exp` substitution type `subst` and its operations and
properties.

-/

import .core

import data.finset.fresh

open [class] [notation] finset
open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `finset V` is the type of a finite set of variable names with freshness.
variables [finset.has_fresh V]

-- `X` and `Y` are finite sets of variable names.
variables {X Y : finset V}

namespace exp -- ===============================================================

-- The type of substitutions.
definition subst (X Y : finset V) : Type :=
  ν∈ X → exp Y

-- Identity substitution construction
definition subst_id (X : finset V) : subst X X :=
  by exact var

-- Update substitution construction
definition subst_update (a : V) (e : exp Y) (F : subst X Y) : subst ('{a} ∪ X) Y :=
  λ x : ν∈ '{a} ∪ X, if P : x.1 = a then e else F (cvar.erase x P)

-- An update for substituting one variable for another.
definition subst_update_var (a b : V) (F : subst X Y) : subst ('{a} ∪ X) ('{b} ∪ Y) :=
  subst_update a (var (cvar.self b Y)) (insert_var b ∘ F)

-- Underlying implemention of `subst_apply`.
definition subst_apply_core (e : exp X) : ∀ {Y : finset V}, subst X Y → exp Y :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      intro Y F,
      exact F x
    end,
    begin /- app -/
      intro Y F,
      exact app (rf F) (re F)
    end,
    begin /- lam -/
      intro Y F,
      have y : V, from (finset.fresh Y).1,
      exact lam $ r (subst_update_var x y F)
    end
  end

-- Apply a substitution to one expression to get another with different free
-- variables.
definition subst_apply : subst X Y → exp X → exp Y :=
  λ F e, subst_apply_core e F

-- Apply a single-variable substitution
definition subst_single (x : V) (e : exp X) : exp ('{x} ∪ X) → exp X :=
  subst_apply $ subst_update x e $ subst_id X

-- Substitution is applied to variables
theorem subst_apply_var (F : subst X Y) (x : ν∈ X)
: subst_apply F (var x) = F x :=
  rfl

-- Substitution distributes over application
theorem subst_distrib_app (F : subst X Y) (f e : exp X)
: subst_apply F (app f e) = app (subst_apply F f) (subst_apply F e) :=
  rfl

-- Substitution distributes over lambda abstraction
theorem subst_distrib_lam (F : subst X Y) (a : V) (e : exp ('{a} ∪ X))
: subst_apply F (lam e) = lam (subst_apply (subst_update_var a (finset.fresh Y).1 F) e) :=
  rfl

end exp -- namespace -----------------------------------------------------------

-- Global attributes
attribute exp.subst            [reducible]
attribute exp.subst_id         [reducible]
attribute exp.subst_update     [reducible]
attribute exp.subst_update_var [reducible]
attribute exp.subst_apply      [reducible]
attribute exp.subst_single     [reducible]
