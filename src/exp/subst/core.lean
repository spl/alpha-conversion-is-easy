/-

This files defines core `subst` definitions.

-/

import .type
import exp.map

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------
namespace subst ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- Identity substitution construction
@[reducible]
protected
def id (X : vs V) : subst X X :=
  var

-- Update a given substitution with a new variable substitution
@[reducible]
protected
def update (a b : V) (F : subst X Y) : subst (insert a X) (insert b Y) :=
  λ (x : ν∈ insert a X),
  if x_eq_a : x.1 = a then
    var (vname.insert_self b Y)
  else
    insert_var b (F (vname.erase x x_eq_a))

-- Apply a substitution to one expression to get another with different free
-- variables.
@[reducible]
protected
def apply : subst X Y → exp X → exp Y :=
  begin
    intros F e,
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r
      generalizing F Y,
    begin /- var -/
      exact F x
    end,
    begin /- app -/
      exact app (rf F) (re F)
    end,
    begin /- lam -/
      have y : V, from (fresh Y).1,
      exact lam (r (subst.update x y F))
    end
  end

namespace apply ----------------------------------------------------------------

section ------------------------------------------------------------------------
variables {F : subst X Y}

/-
These are some useful equalities for targeted rewriting.
-/

theorem of_var (x : ν∈ X) : subst.apply F (var x) = F x :=
  rfl

theorem of_app (f e : exp X)
: subst.apply F (app f e) = app (subst.apply F f) (subst.apply F e) :=
  rfl

theorem of_lam (e : exp (insert a X))
: subst.apply F (lam e) = lam (subst.apply (subst.update a (fresh Y).1 F) e) :=
  rfl

end /- section -/ --------------------------------------------------------------

end /- namespace -/ apply ------------------------------------------------------

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
