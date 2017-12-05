/-

This file contains the type `aexp` for the alpha-equivalent class of `exp`.

-/

import aeq
import logic.basic
import data.category

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

-- Not needed?
@[reducible]
protected
def eq (α₁ : aexp X) (α₂ : aexp X) : Prop :=
  quotient.lift_on₂ α₁ α₂ aeq.id $
    λ e₁ e₂ e₃ e₄ e₁_aeq_e₃ e₂_aeq_e₄, propext $
      iff.intro (λ e₁_aeq_e₂, aeq.id.trans _ (aeq.id.trans _ (aeq.id.symm _ e₁_aeq_e₃) e₁_aeq_e₂) e₂_aeq_e₄)
                (λ e₃_aeq_e₄, aeq.id.trans _ e₁_aeq_e₃ (aeq.id.trans _ e₃_aeq_e₄ (aeq.id.symm _ e₂_aeq_e₄)))

instance decidable_eq : decidable_eq (aexp X) :=
  by apply_instance

-- An `aexp` substitution is a strict wrapper around an `exp` substitution. We
-- use a structure to allow us to convert to and from as necessary.
protected
structure subst (X Y : vs V) : Type :=
  mk :: (as_exp : exp.subst X Y)

@[reducible]
protected
def subst.id (X : vs V) : aexp.subst X X :=
  ⟨exp.subst.id X⟩

@[reducible]
protected
def subst.app : aexp.subst X Y → ν∈ X → aexp Y :=
  λ F x, aexp.of_exp (F.as_exp x)

instance has_comp : has_comp aexp.subst :=
  { comp :=
      λ (X Y Z : vs V) (G : aexp.subst Y Z) (F : aexp.subst X Y),
      ⟨exp.subst.apply G.as_exp ∘ F.as_exp⟩
  }

theorem eq_of_aeq (F : exp.subst X Y) (e₁ e₂ : exp X)
: e₁ ≡α e₂
→ (aexp.of_exp ∘ exp.subst.apply F) e₁ = (aexp.of_exp ∘ exp.subst.apply F) e₂ :=
  quotient.sound ∘ aeq.subst_preservation.id₁ F

theorem eq_of_aeq₂ (F : exp.subst X Y) (G : exp.subst X Y)
(ext : aeq.extend F G (vrel.id X) (vrel.id Y))
(e₁ e₂ : exp X)
: e₁ ≡α e₂
→ (aexp.of_exp ∘ exp.subst.apply F) e₁ = (aexp.of_exp ∘ exp.subst.apply G) e₂ :=
  quotient.sound ∘ aeq.subst_preservation.id F G ext

@[reducible]
protected
def subst.apply : aexp.subst X Y → aexp X → aexp Y
  | ⟨F⟩ := quotient.lift (aexp.of_exp ∘ exp.subst.apply F) (eq_of_aeq F)

@[reducible]
protected
def subst.eq (F : aexp.subst X Y) (G : aexp.subst X Y) : Prop :=
  subst.app F = subst.app G

-- Reflexive
protected
theorem subst.refl : reflexive (@subst.eq _ _ _ _ X Y) :=
  by simp [reflexive, subst.eq]

-- Symmetric
protected
theorem subst.symm : symmetric (@subst.eq _ _ _ _ X Y) :=
  by simp [symmetric, subst.eq]; intros F G; exact eq.symm

-- Transitive
protected
theorem subst.trans : transitive (@subst.eq _ _ _ _ X Y) :=
  by simp [transitive, subst.eq]; intros F G H; exact eq.trans

-- Equivalence
protected
theorem subst.equiv : equivalence (@subst.eq _ _ _ _ X Y) :=
  mk_equivalence (@subst.eq _ _ _ _ X Y) subst.refl subst.symm subst.trans

-- Setoid
instance subst.setoid (X Y : vs V) : setoid (aexp.subst X Y) :=
  setoid.mk (@subst.eq _ _ _ _ X Y) subst.equiv

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
