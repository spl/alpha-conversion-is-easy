import data.set

open set

inductive aeq : set (ℕ × ℕ)  → Type :=
  | var : Π R    x y, (x, y) ∈ R          → aeq R
  | app : Π {R}     , aeq R → aeq R       → aeq R
  | lam : Π {R}  x y, aeq (R \ '{(x, y)}) → aeq R
