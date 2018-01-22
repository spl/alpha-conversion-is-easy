/-

This file contains declarations related to `aeq` identity or reflexivity.

-/

import .equiv

namespace acie -----------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets

-- Identity `aeq` with an implicit `vset`.
@[inline, reducible]
protected
def id {X : vs V} : exp X → exp X → Prop :=
  aeq (vrel.id X)

-- Notation for `aeq.id`.
infix ` ≡α `:50 := aeq.id

namespace id -------------------------------------------------------------------
-- Paper: Corollary 3

-- Reflexivity of `aeq.id`
@[refl]
protected
theorem refl {X : vs V} : ∀ (e : exp X), aeq (vrel.id X) e e :=
  aeq.refl

-- Symmetry of `aeq.id`
@[symm]
protected
theorem symm {X : vs V} ⦃e₁ e₂ : exp X⦄
: aeq (vrel.id X) e₁ e₂ → aeq (vrel.id X) e₂ e₁ :=
  λ a, map.simple (λ x₁ x₂, vrel.inv.of_id) (aeq.symm a)

-- Transitivity of `aeq.id`
@[trans]
protected
theorem trans {X : vs V} ⦃e₁ e₂ e₃ : exp X⦄
: aeq (vrel.id X) e₁ e₂ → aeq (vrel.id X) e₂ e₃ → aeq (vrel.id X) e₁ e₃ :=
  λ a₁ a₂, map.simple (λ x₁ x₂, vrel.id.of_comp) (aeq.trans a₁ a₂)

-- Equivalence
protected
theorem equiv (X : vs V) : equivalence (aeq (vrel.id X)) :=
  mk_equivalence (aeq (vrel.id X))
    (@id.refl _ _ _ _ X)
    (@id.symm _ _ _ _ X)
    (@id.trans _ _ _ _ X)

-- Setoid
instance setoid (X : vs V) : setoid (exp X) :=
  setoid.mk (aeq (vrel.id X)) (id.equiv X)

end /- namespace -/ id ---------------------------------------------------------

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
