/-

This file contains properties for `aexp`.

-/

import .type

namespace acie -----------------------------------------------------------------
namespace aexp -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

-- Paper: Proposition 6.1 (b)
theorem self_eq_subst_id_self (α : aexp X)
: α = aexp.subst.apply (exp.subst.id X) α :=
  quot.induction_on α $ λ e, quot.sound $ aeq.self_aeq_subst_id_self e

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
