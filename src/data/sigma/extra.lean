/-

This file contains extra definitions and theorems for `sigma` and `psigma`.

-/

variables {A : Type} {B : A → Type}
variables {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

namespace psigma

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

end psigma -- namespace
