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
  if p : x.1 = a then
    var (vname.insert_self b Y)
  else
    insert_var b (F (vname.erase x p))

protected
theorem update.eq {a b : V} {F : subst X Y} (x : ν∈ insert a X) (p : x.1 = a)
: subst.update a b F x = var (vname.insert_self b Y) :=
  by simp [subst.update, dif_pos p]

protected
theorem update.ne {a b : V} {F : subst X Y} (x : ν∈ insert a X) (p : x.1 ≠ a)
: subst.update a b F x = insert_var b (F (vname.erase x p)) :=
  by simp [subst.update, dif_neg p]

-- Apply a substitution to one expression to get another with different free
-- variables.
@[reducible]
protected
def apply : ∀ {X Y : vs V}, subst X Y → exp X → exp Y
  | X Y F (var x)              := F x
  | X Y F (app f e)            := app (apply F f) (apply F e)
  | X Y F (@lam _ _ _ _ _ a e) := lam (apply (subst.update a (fresh Y).1 F) e)

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
