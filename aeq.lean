import data.set
import symm_update
import exp

open nat
open set

inductive aeq₁ : set (ℕ × ℕ)  → Type :=
  | var : Π R    x y, (x, y) ∈ R                → aeq₁ R
  | app : Π {R}     , aeq₁ R → aeq₁ R           → aeq₁ R
  | lam : Π {R}  x y, aeq₁ (symm_update₁ R x y) → aeq₁ R

inductive aeq₂ : Π (X : set ℕ) (Y : set ℕ), sset X Y → Type :=
  | var : Π {X Y R} x y, sset.mem x y R                                     → aeq₂ X Y R
  | app : Π {X Y R}    , aeq₂ X Y R → aeq₂ X Y R                            → aeq₂ X Y R
  | lam : Π {X Y R} x y, aeq₂ (insert x X) (insert y Y) (symm_update R x y) → aeq₂ X Y R

open sset
open exp₂
open aeq₂

definition map_aeq₂ : ∀{X Y R S}, (∀{x y}, mem x y R → mem x y S) → aeq₂ X Y R → aeq₂ X Y S
  | X Y R S f (var x y x_y_mem_R) := var x y (@f x y x_y_mem_R)
  | X Y R S f (app e₁ e₂)         := app (map_aeq₂ f e₁) (map_aeq₂ f e₂)
  | X Y R S f (lam x y e)         := lam x y (map_aeq₂ (λ a b, @map_symm_update _ _ _ a b x y _ _ f) e)

theorem aeq_id : ∀{X}, exp₂ X → aeq₂ X X (id X)
  | X (var x x_mem_X) := var x x (and.intro x_mem_X (and.intro x_mem_X (and.intro rfl x_mem_X)))
  | X (app e₁ e₂)     := app (aeq_id e₁) (aeq_id e₂)
  | X (lam x e)       := lam x x (map_aeq₂ (λ a b, iff.elim_right (@mem_symm_update_id _ _ _ a b _)) (aeq_id e))
