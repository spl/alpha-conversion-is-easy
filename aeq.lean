import data.finset

import exp
import symm_update

open exp
open finset
open nat
open sset

inductive aeq : Π{X Y}, sset X Y → exp X → exp Y → Type :=
  | var : Π{X Y} {R : sset X Y} x y (m : sset.mem x y R),                                                            aeq R (var x (mem_left m)) (var y (mem_right m))
  | app : Π{X Y} {R : sset X Y} {f₁ e₁ : exp X} {f₂ e₂ : exp Y}, aeq R f₁ f₂ → aeq R e₁ e₂                         → aeq R (app f₁ e₁)          (app f₂ e₂)
  | lam : Π{X Y} {R : sset X Y} x y {e₁ : exp (insert x X)} {e₂ : exp (insert y Y)}, aeq (symm_update R x y) e₁ e₂ → aeq R (lam x e₁)           (lam y e₂)

open aeq

definition aeq_left  {X Y} {R : sset X Y} {e₁ e₂} : aeq R e₁ e₂ → exp X := λ a, e₁
definition aeq_right {X Y} {R : sset X Y} {e₁ e₂} : aeq R e₁ e₂ → exp Y := λ a, e₂

definition aeq.map
: ∀{X Y} {R : sset X Y} {S : sset X Y} {e₁ : exp X} {e₂ : exp Y}
, (∀{x y}, mem x y R → mem x y S) → aeq R e₁ e₂ → aeq S e₁ e₂ :=
  begin
    intro X Y R S e₁ e₂ f H,
    induction H with
      /- var -/ X Y R x y x_y_mem_R
      /- app -/ X Y R f₁ e₁ f₂ e₂ a₁ a₂ r₁ r₂
      /- lam -/ X Y R x y e₁ e₂ a r,
    begin /- var -/
      have x_y_mem_S : mem x y S, from f x_y_mem_R,
      exact var x y x_y_mem_S
    end,
    begin /- app -/
      have a₁' : aeq S f₁ f₂, from r₁ @f,
      have a₂' : aeq S e₁ e₂, from r₂ @f,
      exact app a₁' a₂'
    end,
    begin /- lam -/
      have f' : ∀ a b, mem a b (symm_update R x y) → mem a b (symm_update S x y), from
        λ a b, map_symm_update @f,
      have a' : aeq (symm_update S x y) e₁ e₂, from r f',
      exact lam x y a'
    end,
  end

theorem aeq.id {X} (e : exp X) : aeq (id X) e e :=
  begin
    induction e with
      /- var -/ X x x_mem_X
      /- app -/ X e₁ e₂ r₁ r₂
      /- lam -/ X x e r,
    begin /- var -/
      have x_x_mem_X : mem x x (id X), from
        and.intro x_mem_X (and.intro x_mem_X (and.intro rfl x_mem_X)),
      exact var x x x_x_mem_X
    end,
    begin /- app -/
      have a₁ : aeq (id X) e₁ e₁, from r₁,
      have a₂ : aeq (id X) e₂ e₂, from r₂,
      exact app a₁ a₂
    end,
    begin /- lam -/
      have f : ∀ a b, mem a b (id (insert x X)) → mem a b (symm_update (id X) x x), from
        λ a b, iff.elim_right mem_symm_update_id,
      have a : aeq (id (insert x X)) e e, from r,
      exact lam x x (aeq.map f a)
    end,
  end

definition aeq.inverse
: ∀{X Y} {R : sset X Y} {e₁ : exp X} {e₂ : exp Y}
, aeq R e₁ e₂ → aeq (inverse R) e₂ e₁ :=
  begin
    intro X Y R e₁ e₂ H,
    induction H with
      /- var -/ X Y R x y x_y_mem_R
      /- app -/ X Y R f₁ e₁ f₂ e₂ a₁ a₂ r₁ r₂
      /- lam -/ X Y R x y e₁ e₂ a r,
    begin /- var -/
      have y_x_mem_inverse_R : mem y x (inverse R), from mem_inverse x_y_mem_R,
      exact var y x y_x_mem_inverse_R
    end,
    begin /- app -/
      have a₁' : aeq (inverse R) f₂ f₁, from r₁,
      have a₂' : aeq (inverse R) e₂ e₁, from r₂,
      exact app a₁' a₂'
    end,
    begin /- lam -/
      have f : ∀ a b,  mem a b (inverse (symm_update R x y))
             → mem a b (symm_update (inverse R) y x), from
        λ a b, iff.elim_left mem_symm_update_inverse,
      have a' : aeq (symm_update (inverse R) y x) e₂ e₁, from aeq.map f r,
      exact lam y x a'
    end,
  end

private
theorem aeq.compose_core
: ∀{X Y} {R : sset X Y} {e₁ : exp X} {e₂ : exp Y}, aeq R e₁ e₂
→ ∀{Z} {S : sset Y Z} {e₂' : exp Y} {e₃ : exp Z}
, e₂ = e₂' →  aeq S e₂' e₃ → aeq (compose R S) e₁ e₃ :=
  begin
    intro X Y R p_e₁ p_e₂ H₁,
    induction H₁ with
      /- var -/ X Y R x y x_y_mem_R
      /- app -/ X Y R f₁ e₁ f₂ e₂ a₁ a₂ r₁ r₂
      /- lam -/ X Y R x y e₁ e₂ a₁ r,
    begin /- H₁: var -/
      intro Z S p_e₂' p_e₃ P H₂,
      cases H₂ with
        /- var -/ Y Z S y' z y_z_mem_S
        /- app -/ Y Z S f₂' e₂' f₃ e₃ a₃ a₄
        /- lam -/ Y Z S y' z e₂' e₃ a₂,
      begin /- H₂: var -/
        have y_eq_y' : y = y', from exp.no_confusion P (λ P₁ P₂ P₃, P₂),
        induction y_eq_y',
        have x_z_mem_compose_R_S : mem x z (compose R S), from
          iff.elim_left mem_compose (exists.intro y (and.intro x_y_mem_R y_z_mem_S)),
        exact var x z x_z_mem_compose_R_S
      end,
      begin /- H₂: app -/
        exact exp.no_confusion P
      end,
      begin /- H₂: lam -/
        exact exp.no_confusion P
      end
    end,
    begin /- H₁: app -/
      intro Z S p_e₂' p_e₃ P H₂,
      cases H₂ with
        /- var -/ Y Z S y' z y_z_mem_S
        /- app -/ Y Z S f₂' e₂' f₃ e₃ a₃ a₄
        /- lam -/ Y Z S y' z e₂' e₃ a₂,
      begin /- H₂: var -/
        exact exp.no_confusion P
      end,
      begin /- H₂: app -/
        have f₂_eq_f₂' : f₂ = f₂', from
          eq_of_heq (exp.no_confusion P (λ P₁ P₂ P₃, P₂)),
        have e₂_eq_e₂' : e₂ = e₂', from
          eq_of_heq (exp.no_confusion P (λ P₁ P₂ P₃, P₃)),
        have a_f₁_f₃ : aeq (compose R S) f₁ f₃, from r₁ f₂_eq_f₂' a₃,
        have a_e₁_f₃ : aeq (compose R S) e₁ e₃, from r₂ e₂_eq_e₂' a₄,
        exact app a_f₁_f₃ a_e₁_f₃
      end,
      begin /- H₂: lam -/
        exact exp.no_confusion P
      end
    end,
    begin /- H₁: lam -/
      intro Z S p_e₂' p_e₃ P H₂,
      cases H₂ with
        /- var -/ Y Z S y' z y_z_mem_S
        /- app -/ Y Z S f₂' e₂' f₃ e₃ a₃ a₄
        /- lam -/ Y Z S y' z e₂' e₃ a₂,
      begin /- H₂: var -/
        exact exp.no_confusion P
      end,
      begin /- H₂: app -/
        exact exp.no_confusion P
      end,
      begin /- H₂: lam -/
        have y_eq_y' : y = y', from exp.no_confusion P (λ P₁ P₂ P₃, P₂),
        induction y_eq_y',
        have e₂_eq_e₂' : e₂ = e₂', from
          eq_of_heq (exp.no_confusion P (λ P₁ P₂ P₃, P₃)),
        have a_e₁_e₃ : aeq (compose (symm_update R x y) (symm_update S y z)) e₁ e₃, from
          r e₂_eq_e₂' a₂,
        have f : ∀ a c, mem a c (compose (symm_update R x y) (symm_update S y z))
               → mem a c (symm_update (compose R S) x z), from
          λ a c, mem_symm_update_compose_of_mem_compose_symm_update,
        have a_e₁_e₃' : aeq (symm_update (compose R S) x z) e₁ e₃, from
          aeq.map f a_e₁_e₃,
        exact lam x z a_e₁_e₃',
      end
    end
  end

theorem aeq.compose {X Y Z} {R : sset X Y} {S : sset Y Z}
{e₁ : exp X} {e₂ : exp Y} {e₃ : exp Z}
(a_e₁_e₂ : aeq R e₁ e₂) (a_e₂_e₃ : aeq S e₂ e₃) : aeq (compose R S) e₁ e₃ :=
  @aeq.compose_core X Y R e₁ e₂ a_e₁_e₂ Z S e₂ e₃ rfl a_e₂_e₃

theorem aeq.reflexive {X} {e : exp X} : aeq (id X) e e := !aeq.id

theorem aeq.symmetric {X} {e₁ e₂ : exp X} (a : aeq (id X) e₁ e₂) : aeq (id X) e₂ e₁ :=
  aeq.map mem_id_of_mem_inverse_id (aeq.inverse a)

theorem aeq.transitive {X} {e₁ e₂ e₃ : exp X} (a₁ : aeq (id X) e₁ e₂) (a₂ : aeq (id X) e₂ e₃) : aeq (id X) e₁ e₃ :=
  aeq.map mem_id_of_mem_compose_id (aeq.compose a₁ a₂)
