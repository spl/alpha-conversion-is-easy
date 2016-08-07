import data.set

open set

inductive exp₁ : set ℕ → Type :=
  | var : Π      x,                   exp₁ '{x}
  | app : Π {X Y} , exp₁ X → exp₁ Y → exp₁ (X ∪ Y)
  | lam : Π {X}  x, exp₁ X          → exp₁ (X \ '{x})

inductive exp₂ : set ℕ → Type :=
  | var : Π X    x, x ∈ X           → exp₂ X
  | app : Π {X}   , exp₂ X → exp₂ X → exp₂ X
  | lam : Π {X}  x, exp₂ (X ∪ '{x}) → exp₂ X
