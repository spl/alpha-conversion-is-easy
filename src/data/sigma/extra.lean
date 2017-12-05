/-

This file contains extra definitions and theorems for `sigma` and `psigma`.

-/

universes u v

namespace psigma ---------------------------------------------------------------

variables {A : Sort u} {B : A → Sort v} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

instance decidable_eq [h₁ : decidable_eq A] [h₂ : ∀a, decidable_eq (B a)] : decidable_eq (psigma B)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n e₁))
  end

@[simp]
theorem fst.unwrap (a : A) (b : B a) : (psigma.mk a b).fst = a :=
  rfl

@[simp]
theorem snd.unwrap (a : A) (b : B a) : (psigma.mk a b).snd = b :=
  rfl

theorem fst.eq (P : psigma.mk a₁ b₁ = psigma.mk a₂ b₂) : a₁ = a₂ :=
  psigma.no_confusion P (λ H₁ H₂, H₁)

theorem snd.heq (P : psigma.mk a₁ b₁ = psigma.mk a₂ b₂) : b₁ == b₂ :=
  psigma.no_confusion P (λ H₁ H₂, H₂)

end /- namespace -/ psigma -----------------------------------------------------
