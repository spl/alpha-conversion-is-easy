/-

This file contains extra definitions and theorems for `sigma`.

-/

open [notation] sigma.ops

namespace sigma -- =============================================================

variables {A : Type} {B : A → Type}

theorem eq₁ (a : A) (b : B a) : ⟨a, b⟩.1 = a :=
  rfl

theorem eq₂ (a : A) (b : B a) : ⟨a, b⟩.2 = b :=
  rfl

end sigma -- namespace ---------------------------------------------------------
