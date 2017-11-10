/-

This file contains properties for `aexp`.

-/

import .type

namespace acie -----------------------------------------------------------------
namespace aexp -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- Paper: Proposition 6.1 (b)
theorem self_eq_subst_var_self (α : aexp X)
: α = aexp.subst.apply exp.var α :=
  quot.induction_on α $ λ e, quot.sound $ aeq.self_aeq_subst_var e

-- Paper: Proposition 6.2
theorem subst_F_comp_var_eq_F (F : exp.subst X Y) (x : ν∈ X)
: aexp.subst.apply F (aexp.of_exp (exp.var x)) = aexp.of_exp (F x) :=
  by apply quot.lift_beta (aexp.of_exp ∘ exp.subst.apply F) (eq_of_aeq_id F) (exp.var x)

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
