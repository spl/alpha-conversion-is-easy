import data.finset
import data.finset.fresh

import exp

open exp
open finset
open nat

definition subst (X Y : finset ℕ) : Type₁ := ∀ x, x ∈ X → exp Y

variables {X Y : finset ℕ}

definition subst.id (X) : subst X X := var

definition subst.update (x e) (f : subst X Y) : subst (insert x X) Y :=
  assume x' (x'_mem_insert_x_X : x' ∈ insert x X),
  if P : x' = x then
    e
  else
    have x'_mem_X : x' ∈ X, from
      finset.mem_of_mem_insert_of_ne x'_mem_insert_x_X P,
    f x' x'_mem_X

definition subst.update_var (x y : ℕ) (f : subst X Y) : subst (insert x X) (insert y Y) :=
  subst.update x
    (var y (finset.mem_insert y Y))
    (λ x' x'_mem_X, exp.insert y (f x' x'_mem_X))

private
definition subst.apply_core (e : exp X) : ∀ {Y}, (subst X Y) → exp Y :=
  begin
    induction e with
      /- var -/ X x x_mem_X
      /- app -/ X e₁ e₂ r₁ r₂
      /- lam -/ X x e r,
    begin /- e: exp.var -/
      intro Y f,
      exact f x x_mem_X
    end,
    begin /- e: exp.app -/
      intro Y f,
      exact app (r₁ f) (r₂ f)
    end,
    begin /- e: exp.lam -/
      intro Y f,
      have y : ℕ, from fresh Y,
      have e' : exp (insert y Y), from r (subst.update_var x y f),
      exact lam y e'
    end
  end

definition subst.apply : subst X Y → exp X → exp Y :=
  λ f e, @subst.apply_core X e Y f

definition subst.single (x) (e : exp X) : exp (insert x X) → exp X :=
  subst.apply (subst.update x e (subst.id X))
