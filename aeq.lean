import data.set
import symm_update
import exp

open nat
open set
open sset
open exp

inductive aeq : Π{X Y}, sset X Y → exp X → exp Y → Type :=
  | var : Π{X Y} {R : sset X Y} x y (m : sset.mem x y R),                                                            aeq R (var x (mem_left m)) (var y (mem_right m))
  | app : Π{X Y} {R : sset X Y} {f₁ e₁ : exp X} {f₂ e₂ : exp Y}, aeq R f₁ f₂ → aeq R e₁ e₂                         → aeq R (app f₁ e₁)          (app f₂ e₂)
  | lam : Π{X Y} {R : sset X Y} x y {e₁ : exp (insert x X)} {e₂ : exp (insert y Y)}, aeq (symm_update R x y) e₁ e₂ → aeq R (lam x e₁)           (lam y e₂)

open aeq

definition aeq_left  {X Y} {R : sset X Y} {e₁ e₂} : aeq R e₁ e₂ → exp X := λ a, e₁
definition aeq_right {X Y} {R : sset X Y} {e₁ e₂} : aeq R e₁ e₂ → exp Y := λ a, e₂

definition aeq.map
: ∀{X Y} {R : sset X Y} {S : sset X Y} {e₁ : exp X} {e₂ : exp Y}
, (∀{x y}, mem x y R → mem x y S)
→ aeq R e₁ e₂ → aeq S e₁ e₂
  | X Y R S (var x x_mem_X) (var y y_mem_Y) f (var x y x_y_mem_R) := var x y (@f x y x_y_mem_R)
  | X Y R S (app f₁ e₁)     (app f₂ e₂)     f (app a₁ a₂)         := app (aeq.map f a₁) (aeq.map f a₂)
  | X Y R S (lam x e₁)      (lam y e₂)      f (lam x y a)         :=
    have f' : ∀ a b, mem a b (symm_update R x y) → mem a b (symm_update S x y), from
      λ a b, map_symm_update f,
    lam x y (aeq.map f' a)

theorem aeq.id : ∀{X} (e : exp X), aeq (id X) e e
  | X (var x x_mem_X) := var x x (and.intro x_mem_X (and.intro x_mem_X (and.intro rfl x_mem_X)))
  | X (app e₁ e₂)     := app (aeq.id e₁) (aeq.id e₂)
  | X (lam x e)       :=
    have f : ∀ a b, mem a b (id (insert x X)) → mem a b (symm_update (id X) x x), from
      λ a b, iff.elim_right mem_symm_update_id,
    lam x x (aeq.map f (aeq.id e))

theorem aeq.inverse : ∀{X Y} {R : sset X Y} {e₁ e₂}, aeq R e₁ e₂ → aeq (inverse R) e₂ e₁
  | X Y R (var x x_mem_X) (var y y_mem_Y) (var x y x_y_mem_R) := var y x (mem_inverse x_y_mem_R)
  | X Y R (app f₁ e₁)     (app f₂ e₂)     (app a₁ a₂)         := app (aeq.inverse a₁) (aeq.inverse a₂)
  | X Y R (lam x e)       (lam y e₂)      (lam x y a)         :=
    have f : ∀ a b,  mem a b (inverse (symm_update R x y))
           → mem a b (symm_update (inverse R) y x), from
      λ a b, iff.elim_left mem_symm_update_inverse,
    lam y x (aeq.map f (aeq.inverse a))

theorem aeq.compose
: ∀{X Y Z} {R : sset X Y} {S : sset Y Z} {e₁ e₂ e₃}
, aeq R e₁ e₂ → aeq S e₂ e₃ → aeq (compose R S) e₁ e₃
  | X Y Z R S (var x x_mem_X) (var y y_mem_Y) (var z z_mem_Z) (var x y x_y_mem_R) (var y z y_z_mem_S) :=
    var x z (iff.elim_left mem_compose (exists.intro y (and.intro x_y_mem_R y_z_mem_S)))
  | X Y Z R S (app f₁ e₁)     (app f₂ e₂)     (app f₃ e₃)     (app a₁ a₂)         (app a₃ a₄)         :=
    app (aeq.compose a₁ a₃) (aeq.compose a₂ a₄)
  | X Y Z R S (lam x e)       (lam y e₂)      (lam z e₃)      (lam x y a₁)        (lam y z a₂)        :=
    have f : ∀ a c, mem a c (compose (symm_update R x y) (symm_update S y z))
           → mem a c (symm_update (compose R S) x z), from
      λ a c, mem_symm_update_compose_of_mem_compose_symm_update,
    lam x z (aeq.map f (aeq.compose a₁ a₂))

theorem aeq.reflexive {X} {e : exp X} : aeq (id X) e e := !aeq.id

theorem aeq.symmetric {X} {e₁ e₂ : exp X} (a : aeq (id X) e₁ e₂) : aeq (id X) e₂ e₁ :=
  aeq.map mem_id_of_mem_inverse_id (aeq.inverse a)

theorem aeq.transitive {X} {e₁ e₂ e₃ : exp X} (a₁ : aeq (id X) e₁ e₂) (a₂ : aeq (id X) e₂ e₃) : aeq (id X) e₁ e₃ :=
  aeq.map mem_id_of_mem_compose_id (aeq.compose a₁ a₂)
