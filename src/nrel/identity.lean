/-

This file contains the `nrel.is_identity` class and instances.

-/

import .id
import .inv
import .comp
import .update

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X : finset V}

namespace alpha

namespace nrel

-- `identity R` is a type class for `R : X ×ν X` that witnesses the isomorphism
-- between `R` and `id X`. This class allows the use of more general identities
-- than those strictly defined by `eq`, as `id` is.
class is_identity (R : X ×ν X) : Prop :=
  (to_id   : ∀ {x₁ x₂ : ν∈ X}, ⟪x₁, x₂⟫ ∈ν R → ⟪x₁, x₂⟫ ∈ν nrel.id X)
  (from_id : ∀ {x₁ x₂ : ν∈ X}, ⟪x₁, x₂⟫ ∈ν nrel.id X → ⟪x₁, x₂⟫ ∈ν R)

instance id.is_identity : is_identity (nrel.id X) :=
  { to_id   := λ x₁ x₂, id
  , from_id := λ x₁ x₂, id
  }

instance inv.is_identity (R : X ×ν X) [is_identity R] : is_identity R⁻¹ :=
  { to_id   := λ x₁ x₂, eq.symm ∘ is_identity.to_id X ∘ nrel.symm
  , from_id := λ x₁ x₂, nrel.symm ∘ is_identity.from_id R ∘ eq.symm
  }

instance comp.is_identity (R : X ×ν X) (S : X ×ν X) [is_identity R] [is_identity S]
: is_identity (R ⨾ S) :=
  { to_id :=
      begin
        intros x₁ x₃ P,
        cases P with x₂ P,
        cases P with x₁_R_x₂ x₂_S_x₃,
        exact eq.trans (is_identity.to_id X x₁_R_x₂) (is_identity.to_id X x₂_S_x₃)
      end
  , from_id :=
      begin
        intros x₁ x₃ P,
        existsi x₁,
        split,
        { exact is_identity.from_id R rfl },
        { exact is_identity.from_id S P },
      end
  }

instance update.is_identity (R : X ×ν X) [I : is_identity R] (a : V) : is_identity (R ⩁ (a, a)) :=
  { to_id :=
      begin
        intros x₁ x₂ P,
        cases x₁ with x₁ px₁,
        cases x₂ with x₂ px₂,
        cases P with Peq Pne,
        begin
          cases Peq with x₁_eq_a x₂_eq_a,
          unfold psigma.fst at x₁_eq_a x₂_eq_a,
          rw [←x₂_eq_a] at x₁_eq_a,
          induction x₁_eq_a,
          unfold nrel.id
        end,
        begin
          cases Pne with x₁_ne_a Pne,
          cases Pne with x₂_ne_a x₁_R_x₂,
          unfold psigma.fst at x₁_ne_a x₂_ne_a,
          have H : x₁ = x₂ :=
            psigma.no_confusion (is_identity.to_id X x₁_R_x₂) (λ h₁ h₂, h₁),
          induction H,
          unfold nrel.id
        end
      end
  , from_id :=
      begin
        intros x₁ x₂ P,
        have H : x₁ = x₂ := P,
        induction H,
        cases decidable.em (x₁.1 = a) with x₁1_eq_a x₁1_ne_a,
        begin -- x₁1_eq_a : x₁.1 = a
          left, split, exact x₁1_eq_a, exact x₁1_eq_a
        end,
        begin -- x₁1_ne_a : x₁.1 ≠ a
          right, existsi x₁1_ne_a, existsi x₁1_ne_a, exact is_identity.from_id R rfl
        end
      end
  }

end nrel

end alpha
