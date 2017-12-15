/-

This files defines the `exp` substitution type `subst` and its operations and
properties.

-/

import .core

import data.fresh
import data.sigma.extra

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------
namespace subst ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- Substitution distributes over application
theorem distrib_app (F : subst X Y) (f e : exp X)
: subst.apply F (app f e) = app (subst.apply F f) (subst.apply F e) :=
  rfl

-- Substitution distributes over lambda abstraction
theorem distrib_lam (F : subst X Y) (a : V) (e : exp (insert a X))
: subst.apply F (lam e) = lam (subst.apply (subst.update a (fresh Y).1 F) e) :=
  rfl

theorem update_of_ne (a b : V) (F : subst X Y) (x : ν∈ insert a X) (p : x.1 ≠ a)
: subst.update a b F x = insert_var b (F (vname.erase x p)) :=
  by simp [exp.subst.update, dif_neg p]

theorem update_eq_var_update (a b : V) (F : X →ν Y) (x : ν∈ insert a X)
: subst.update a b (subst.lift F) x = subst.lift (vname.update a b F) x :=
  begin
    cases x with c pc,
    simp [subst.update, subst.lift, function.comp, vname.update],
    cases decidable.em (c = a) with c_eq_a c_ne_a,
    begin /- c_eq_a : c = a -/
      simp [dif_pos c_eq_a]
    end,
    begin /- c_ne_a : c ≠ a -/
      simp [dif_neg c_ne_a, insert_var, map, vname.insert],
      reflexivity
    end
  end

variables {F G : subst X Y} -- Substitutions

-- Substitution variable update distributes over equality.
theorem update_distrib (a b : V)
(P : ∀ (x : ν∈ X), F x = G x) (x : ν∈ insert a X)
: subst.update a b F x = subst.update a b G x :=
  begin
    cases x with c pc,
    simp [subst.update],
    cases decidable.em (c = a) with c_eq_a c_ne_a,
    begin /- c_eq_a : c = a -/
      simp [dif_pos c_eq_a]
    end,
    begin /- c_ne_a : c ≠ a -/
      simp [dif_neg c_ne_a, function.comp],
      rw [P $ vname.erase ⟨c, pc⟩ c_ne_a]
    end
  end

-- Substitution application distributes over equality.
theorem apply_distrib (P : ∀ (x : ν∈ X), F x = G x) (e : exp X)
: subst.apply F e = subst.apply G e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r
      generalizing Y F G P,
    begin /- var -/
      apply P,
    end,
    begin /- app -/
      simp [distrib_app],
      rw [rf P, re P],
    end,
    begin /- lam -/
      simp [distrib_lam],
      rw [r $ update_distrib a (fresh Y).1 P],
    end
  end

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
