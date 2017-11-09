/-

This files defines the `exp` substitution type `subst` and its operations and
properties.

-/

import .core

import data.fresh
import data.sigma.extra

namespace alpha ----------------------------------------------------------------
namespace exp ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- The type of substitutions.
@[reducible]
def subst (X Y : vs V) : Type :=
  ν∈ X → exp Y

-- Lift a function to a substitution
@[reducible]
def subst.lift : (X →ν Y) → subst X Y :=
  λ F, var ∘ F

-- Identity substitution construction
@[reducible]
def subst_id (X : vs V) : subst X X :=
  by exact var

-- Update substitution construction
@[reducible]
def subst_update (a : V) (e : exp Y) (F : subst X Y) : subst (insert a X) Y :=
  λ x : ν∈ insert a X, if P : x.1 = a then e else F (vname.erase x P)

-- An update for substituting one variable for another.
@[reducible]
def subst_update_var (a b : V) (F : subst X Y) : subst (insert a X) (insert b Y) :=
  subst_update a (var (vname.insert_self b Y)) (insert_var b ∘ F)

-- Underlying implemention of `subst_apply`.
def subst_apply_core (e : exp X) : ∀ {Y : vs V}, subst X Y → exp Y :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      intros Y F,
      exact F x
    end,
    begin /- app -/
      intros Y F,
      exact app (rf F) (re F)
    end,
    begin /- lam -/
      intros Y F,
      have y : V, from (fresh Y).1,
      exact lam (r (subst_update_var x y F))
    end
  end

-- Apply a substitution to one expression to get another with different free
-- variables.
@[reducible]
def subst_apply : subst X Y → exp X → exp Y :=
  λ F e, subst_apply_core e F

-- Apply a single-variable substitution
@[reducible]
def subst_single (x : V) (e : exp X) : exp (insert x X) → exp X :=
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
theorem subst_distrib_lam (F : subst X Y) (a : V) (e : exp (insert a X))
: subst_apply F (lam e) = lam (subst_apply (subst_update_var a (fresh Y).1 F) e) :=
  rfl

lemma subst_update_var_eq_var_update (a b : V) (F : X →ν Y) (x : ν∈ insert a X)
: subst_update_var a b (subst.lift F) x = subst.lift (vname.update a b F) x :=
  begin
    cases x with c pc,
    simp [subst_update_var, subst_update, subst.lift, function.comp, vname.update],
    cases decidable.em (c = a) with c_eq_a c_ne_a,
    begin /- c_eq_a : c = a -/
      simp [dif_pos c_eq_a]
    end,
    begin /- c_ne_a : c ≠ a -/
      simp [dif_neg c_ne_a, insert_var, map, map_core, vname.insert],
      reflexivity
    end
  end

theorem subst_update_var_distrib (a b : V)
: ∀ {F G :  subst X Y}, (∀ x : ν∈ X, F x = G x)
→ ∀ x : ν∈ insert a X, subst_update_var a b F x = subst_update_var a b G x :=
  begin
    intros F G F_eq_G x,
    cases x with c pc,
    unfold subst_update_var subst_update,
    cases decidable.em (c = a) with c_eq_a c_ne_a,
    begin /- c_eq_a : c = a -/
      simp [dif_pos c_eq_a]
    end,
    begin /- c_ne_a : c ≠ a -/
      simp [dif_neg c_ne_a, function.comp],
      rw [F_eq_G (vname.erase ⟨c, pc⟩ c_ne_a)]
    end
  end

theorem subst_apply_distrib (e : exp X)
: ∀ {Y : vs V} {F G :  subst X Y}, (∀ x : ν∈ X, F x = G x)
→ subst_apply F e = subst_apply G e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r,
    begin /- var -/
      intros Y F G F_eq_G,
      apply F_eq_G,
    end,
    begin /- app -/
      intros Y F G F_eq_G,
      simp [subst_distrib_app],
      rw [rf F_eq_G, re F_eq_G],
    end,
    begin /- lam -/
      intros Y F G F_eq_G,
      simp [subst_distrib_lam],
      rw [r $ subst_update_var_distrib a (fresh Y).1 F_eq_G],
    end
  end

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ alpha ------------------------------------------------------
