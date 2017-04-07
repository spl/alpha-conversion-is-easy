/-

This file contains extra definitions and theorems for `sigma`.

-/

import data.sigma

open [notation] function
open [notation] sigma.ops

namespace sigma -- =============================================================

variables {A : Type} {B : A → Type}

theorem eq₁ (a : A) (b : B a) : ⟨a, b⟩.1 = a :=
  rfl

theorem eq₂ (a : A) (b : B a) : ⟨a, b⟩.2 = b :=
  rfl

end sigma -- namespace ---------------------------------------------------------

namespace sigma -- =============================================================

variables {A : Type} {B : A → Prop}

theorem eq_of_prop₁ {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (P : a₁ = a₂)
: ⟨a₁, b₁⟩ = ⟨a₂, b₂⟩ :=

  eq_of_heq $ sigma.heq (heq.refl B) (heq_of_eq P) $
    by induction P; exact heq_of_eq (proof_irrel b₁ b₂)

end sigma -- namespace ---------------------------------------------------------
