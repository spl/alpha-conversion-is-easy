/-

This file contains the type `aexp` for the alpha-equivalent class of `exp`.

-/

import aeq

namespace acie -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- The type of alpha-equivalent expressions.
def aexp (X : vs V) : Type :=
  quotient (aeq.id.setoid X)

namespace aexp -----------------------------------------------------------------

@[reducible]
protected
def of_exp : exp X → aexp X :=
  quotient.mk

@[reducible]
def var : ν∈ X → aexp X :=
  aexp.of_exp ∘ exp.var

theorem eq_of_aeq_id (F : exp.subst X Y) (e₁ e₂ : exp X)
: e₁ ≡α e₂
→ (aexp.of_exp ∘ exp.subst.apply F) e₁ = (aexp.of_exp ∘ exp.subst.apply F) e₂ :=
  quotient.sound ∘ aeq.subst_preservation.id₁ F

@[reducible]
protected
def subst.apply (F : exp.subst X Y) : aexp X → aexp Y :=
  quotient.lift (aexp.of_exp ∘ exp.subst.apply F) (eq_of_aeq_id F)

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
