import data.set
import symm_update

open set

inductive aeq₁ : set (ℕ × ℕ)  → Type :=
  | var : Π R    x y, (x, y) ∈ R                → aeq₁ R
  | app : Π {R}     , aeq₁ R → aeq₁ R           → aeq₁ R
  | lam : Π {R}  x y, aeq₁ (symm_update₁ R x y) → aeq₁ R

inductive aeq₂ : Π (X : set ℕ) (Y : set ℕ), sset X Y → Type :=
  | var : Π {X Y R} x y, sset.mem x y R                                      → aeq₂ X Y R
  | app : Π {X Y R}    , aeq₂ X Y R → aeq₂ X Y R                             → aeq₂ X Y R
  | lam : Π {X Y R} x y, aeq₂ (insert x X) (insert y Y) (symm_update₂ R x y) → aeq₂ X Y R
