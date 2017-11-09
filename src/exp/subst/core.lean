/-

This files defines core `subst` definitions.

-/

import .type
import exp.map

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------
namespace subst ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- Identity substitution construction
@[reducible]
protected
def id (X : vs V) : subst X X :=
  var

-- Update substitution construction
@[reducible]
protected
def update (a : V) (e : exp Y) (F : subst X Y) : subst (insert a X) Y :=
  λ (x : ν∈ insert a X), if P : x.1 = a then e else F (vname.erase x P)

-- An update for substituting one variable for another.
@[reducible]
protected
def update_var (a b : V) (F : subst X Y) : subst (insert a X) (insert b Y) :=
  subst.update a (var (vname.insert_self b Y)) (insert_var b ∘ F)

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
      exact lam (r (subst.update_var x y F))
    end
  end

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
