/-

This files defines `subst.apply`.

-/

import .update

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------
namespace subst ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets

-- Apply a substitution to one expression to get another with different free
-- variables.
@[reducible]
protected
def apply : ∀ {X Y : vs V}, subst X Y → exp X → exp Y
  | X Y F (var x)    := F x
  | X Y F (app f e)  := app (apply F f) (apply F e)
  | X Y F (lam' a e) := lam (apply (subst.update a (fresh Y).1 F) e)

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
