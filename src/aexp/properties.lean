/-

This file contains properties for `aexp`.

-/

import .type

namespace acie -----------------------------------------------------------------
namespace aexp -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {W X Y Z : vs V} -- Variable name sets

-- Paper: Proposition 6.1 (b)
theorem self_eq_subst_var_self (α : aexp X)
: α = aexp.subst.apply (aexp.subst.id X) α :=
  quot.induction_on α $ λ e, quot.sound $ aeq.self_aeq_subst_var e

-- Paper: Proposition 6.2
theorem subst_F_comp_var_eq_F (F : aexp.subst X Y)
: aexp.subst.apply F ∘ aexp.subst.app (aexp.subst.id X) = aexp.subst.app F :=
  funext
    begin
      intro x,
      simp [function.comp],
      cases F with F,
      apply quot.lift_beta (aexp.of_exp ∘ exp.subst.apply F) (eq_of_aeq F) (exp.var x)
    end

theorem subst.left_id (F : aexp.subst X Y) : aexp.subst.id Y ∘ F ≈ F :=
  begin
    cases F with F,
    simp [has_comp.comp, setoid.r, subst.eq, subst.app],
    apply funext,
    intro x,
    apply quotient.sound,
    simp [setoid.r, function.comp],
    exact aeq.id.symm _ (aeq.self_aeq_subst_var (F x))
  end

theorem subst.right_id (F : aexp.subst X Y) : F ∘ aexp.subst.id X ≈ F :=
  begin
    cases F with F,
    simp [has_comp.comp, setoid.r, subst.eq]
  end

theorem subst.assoc (H : aexp.subst Y Z) (G : aexp.subst X Y) (F : aexp.subst W X)
: H ∘ (G ∘ F) ≈ (H ∘ G) ∘ F :=
  begin
    cases H with H, cases G with G, cases F with F,
    simp [has_comp.comp, setoid.r, subst.eq, subst.app],
    apply funext,
    intro w,
    apply quotient.sound,
    simp [setoid.r, function.comp],
    exact aeq.subst_comp G H (F w)
  end

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
