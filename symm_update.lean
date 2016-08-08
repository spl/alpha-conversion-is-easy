import data.set

open prod.ops
open set

definition symm_update₁ (R : set (ℕ × ℕ)) (x y : ℕ) : set (ℕ × ℕ) :=
  λ p, p = (x, y) ∨ p.1 ≠ x ∧ p.1 ≠ y ∧ p ∈ R

variable {A : Type}

definition sset (X : set A) (Y : set A) : Type := A → A → Prop

namespace sset

variables {X Y : set A}

definition mem (x y : A) (S : sset X Y) := x ∈ X ∧ y ∈ Y ∧ S x y

definition insert (x y : A) (S : sset X Y) : sset (set.insert x X) (set.insert y Y) :=
  λ v w, v = x ∧ w = y ∨ mem v w S

end sset

definition symm_update₂ {X Y : set ℕ} (R : sset X Y) (x y : ℕ) : sset (insert x X) (insert y Y) :=
  λ v w, v = x ∧ w = y ∨ v ≠ x ∧ v ≠ y ∧ sset.mem v w R
