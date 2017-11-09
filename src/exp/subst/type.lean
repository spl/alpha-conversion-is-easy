/-

This files defines the substitution type `subst`.

-/

import exp.type

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- The type of a substitution
@[reducible]
def subst (X Y : vs V) : Type :=
  ν∈ X → exp Y

-- Lift a function to a substitution
@[reducible]
def subst.lift : (X →ν Y) → subst X Y :=
  function.comp var

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
