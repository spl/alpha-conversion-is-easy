import data.finset

open finset
open nat

inductive exp : finset ℕ → Type :=
  | var : Π {X} x, x ∈ X            → exp X
  | app : Π {X}  , exp X → exp X    → exp X
  | lam : Π {X} x, exp (insert x X) → exp X
