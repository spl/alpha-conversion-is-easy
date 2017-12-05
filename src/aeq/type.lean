/-

This file contains the `aeq` data type.

We put the data type in its own file because it takes a long time to compile and
we want Lean to cache the results.

-/

import exp
import vrel

namespace acie -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets

/-
`aeq R e₁ e₂` is an inductive data type that relates `e₁ : exp X` and `e₂ : exp
Y` via their free variables with `R : X ×ν Y`.
-/

inductive aeq : Π {X Y : vs V}, X ×ν Y → exp X → exp Y → Prop
  | var : Π {X Y : vs V} {R : X ×ν Y}           {x : ν∈ X}              {y : ν∈ Y},              ⟪x, y⟫ ∈ν R →               aeq R (exp.var x)     (exp.var y)
  | app : Π {X Y : vs V} {R : X ×ν Y}           {fX eX : exp X}         {fY eY : exp Y},         aeq R fX fY → aeq R eX eY → aeq R (exp.app fX eX) (exp.app fY eY)
  | lam : Π {X Y : vs V} {R : X ×ν Y} {a b : V} {eX : exp (insert a X)} {eY : exp (insert b Y)}, aeq (R ⩁ (a, b)) eX eY →    aeq R (exp.lam eX)    (exp.lam eY)

-- Notation for `aeq`.
notation e₁ ` ≡α⟨`:50 R `⟩ ` e₂:50 := aeq R e₁ e₂

namespace aeq ------------------------------------------------------------------

variables {X Y : vs V} -- Variable name sets
variables {R : X ×ν Y} -- Variable name set relations

section ------------------------------------------------------------------------
variables {x : ν∈ X} {y : ν∈ Y} -- Variable name set members
protected
def var.prop : aeq R (exp.var x) (exp.var y) → ⟪x, y⟫ ∈ν R
  | (var p) := p
end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {fX eX : exp X} {fY eY : exp Y} -- Expressions
protected
def app.fun : aeq R (exp.app fX eX) (exp.app fY eY) → aeq R fX fY
  | (app f e) := f
protected
def app.arg : aeq R (exp.app fX eX) (exp.app fY eY) → aeq R eX eY
  | (app f e) := e
end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {a b : V} -- Variable names
variables {eX : exp (insert a X)} {eY : exp (insert b Y)} -- Expressions
protected
def lam.body : aeq R (exp.lam eX) (exp.lam eY) → aeq (R ⩁ (a, b)) eX eY
  | (lam e) := e
end /- section -/ --------------------------------------------------------------

open decidable

instance decidable (R : X ×ν Y) [d : ∀ x y, decidable (⟪x, y⟫ ∈ν R)]
(e₁ : exp X) (e₂ : exp Y)
: decidable (e₁ ≡α⟨R⟩ e₂) :=
  begin
    induction e₁ with
      /- var -/ X x
      /- app -/ X f₁ e₁ rf re
      /- lam -/ X a e₁ r
      generalizing Y R d e₂,
    begin /- var -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        cases d x y with not_x_R_y x_R_y,
        begin /- not_x_R_y : ¬R x y -/
          exact is_false (not_x_R_y ∘ var.prop)
        end,
        begin /- x_R_y : R x y -/
          exact is_true (var x_R_y)
        end
      end,
      begin /- app -/
        exact is_false (λ h, by cases h)
      end,
      begin /- lam -/
        exact is_false (λ h, by cases h)
      end
    end,
    begin /- app -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        exact is_false (λ h, by cases h)
      end,
      begin /- app -/
        have hf : decidable (f₁ ≡α⟨R⟩ f₂) := rf R f₂,
        cases hf with hf_f hf_t,
        begin /- hf_f : ¬f₁ ≡α⟨R⟩ f₂ -/
          exact is_false (hf_f ∘ app.fun)
        end,
        begin /- hf_t : f₁ ≡α⟨R⟩ f₂ -/
          have he : decidable (e₁ ≡α⟨R⟩ e₂) := re R e₂,
          cases he with he_f he_t,
          begin /- he_f : ¬e₁ ≡α⟨R⟩ e₂ -/
            exact is_false (he_f ∘ app.arg)
          end,
          begin /- he_t : e₁ ≡α⟨R⟩ e₂ -/
            exact is_true (app hf_t he_t)
          end
        end
      end,
      begin /- lam -/
        exact is_false (λ h, by cases h)
      end
    end,
    begin /- lam -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        exact is_false (λ h, by cases h)
      end,
      begin /- app -/
        exact is_false (λ h, by cases h)
      end,
      begin /- lam -/
          have he : decidable (e₁ ≡α⟨R ⩁ (a, b)⟩ e₂) := r (R ⩁ (a, b)) e₂,
          cases he with he_f he_t,
          begin /- he_f : ¬e₁ ≡α⟨R⟩ e₂ -/
            exact is_false (he_f ∘ lam.body)
          end,
          begin /- he_t : e₁ ≡α⟨R⟩ e₂ -/
            exact is_true (lam he_t)
          end
      end
    end
  end

end /- namespace -/ aeq --------------------------------------------------------

end /- namespace -/ acie -------------------------------------------------------
