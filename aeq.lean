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

definition map_aeq₂
: ∀{X Y X' Y'} {R : sset X Y} {S : sset X' Y'}
, (∀{x y}, mem x y R → mem x y S)
→ aeq₂ X Y R
→ aeq₂ X' Y' S
  | X Y X' Y' R S f (var x y x_y_mem_R) := var x y (@f x y x_y_mem_R)
  | X Y X' Y' R S f (app e₁ e₂)         := app (map_aeq₂ f e₁) (map_aeq₂ f e₂)
  | X Y X' Y' R S f (lam x y e)         :=
    have f' : ∀ a b, mem a b (symm_update R x y) → mem a b (symm_update S x y), from
      λ a b, map_symm_update f,
    lam x y (map_aeq₂ f' e)

theorem aeq_id : ∀{X}, exp₂ X → aeq₂ X X (id X)
  | X (var x x_mem_X) := var x x (and.intro x_mem_X (and.intro x_mem_X (and.intro rfl x_mem_X)))
  | X (app e₁ e₂)     := app (aeq_id e₁) (aeq_id e₂)
  | X (lam x e)       :=
    have f : ∀ a b, mem a b (id (insert x X)) → mem a b (symm_update (id X) x x), from
      λ a b, iff.elim_right mem_symm_update_id,
    lam x x (map_aeq₂ f (aeq_id e))

/-
theorem aeq_id.right : ∀{X}, aeq₂ X X (id X) → exp₂ X
  | X (@aeq₂.var _ _ (id X) x x x_x_mem_X) := var x (mem_left x_x_mem_X)
  | X (app e₁ e₂)         := app (aeq_id.right e₁) (aeq_id.right e₂)
  | X (lam x x e)         :=
    have f : ∀ a b, mem a b (symm_update (id X) x x) → mem a b (id (insert x X)), from
      λ a b, iff.elim_left mem_symm_update_id,
    lam x (aeq_id.right (map_aeq₂ f e))
-/

theorem aeq_inverse : ∀{X Y R}, aeq₂ X Y R → aeq₂ Y X (inverse R)
  | X Y R (var x y x_y_mem_R) := var y x (mem_inverse x_y_mem_R)
  | X Y R (app e₁ e₂)         := app (aeq_inverse e₁) (aeq_inverse e₂)
  | X Y R (lam x y e)         :=
    have f : ∀ a b,  mem a b (inverse (symm_update R x y))
           → mem a b (symm_update (inverse R) y x), from
      λ a b, iff.elim_left mem_symm_update_inverse,
    lam y x (map_aeq₂ f (aeq_inverse e))
