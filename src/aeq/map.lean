/-

This file contains the `aeq` `map` operation.

-/

import .type

namespace acie ----------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X X₂ X₁ Y Y₁ Y₂ : vs V} -- Variable name sets

section ------------------------------------------------------------------------
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂} -- Variable name set relations
variables {eX : exp X₁} {eY : exp Y₁} -- Expressions

-- The `map` implementation for `aeq`.
lemma map_core (H : eX ≡α⟨R⟩ eY)
: ∀ {X₂ Y₂ : vs V} (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
    {S : X₂ ×ν Y₂} (F : R ⇒ν S)
, exp.map pX eX ≡α⟨S⟩ exp.map pY eY :=
  begin
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r,
    begin /- var -/
      intros X₂ Y₂ pX pY S F,
      cases F x y x_R_y with _ H, cases H with _ x_S_y,
      exact var x_S_y
    end,
    begin /- app -/
      intros X₂ Y₂ pX pY S F,
      exact app (rf pX pY F) (re pX pY F)
    end,
    begin /- lam -/
      intros X₂ Y₂ pX pY S F,
      exact (lam $
        r (vset.prop_insert_of_subset _ pX)
          (vset.prop_insert_of_subset _ pY)
          (vrel.map.update x y F))
    end
  end

-- Map alpha-equality from one variable relation, `R : X₁ ×ν Y₁`, to another,
-- `S : X₂ ×ν Y₂`, as long as `X₁ ⊆ X₂` and `Y₁ ⊆ Y₂`.
theorem map (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
: R ⇒ν S → eX ≡α⟨R⟩ eY → exp.map pX eX ≡α⟨S⟩ exp.map pY eY :=
  λ F H, map_core H pX pY F

end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {R S : X ×ν Y} -- Variable name set relations
variables {eX : exp X} {eY : exp Y} -- Expressions

-- A wrapper for `map` in which the free variable sets do not change.
theorem map.simple
: (∀ (x : ν∈ X) (y : ν∈ Y), ⟪x, y⟫ ∈ν R → ⟪x, y⟫ ∈ν S) → eX ≡α⟨R⟩ eY → eX ≡α⟨S⟩ eY :=
  assume F H,
  have F' : R ⇒ν S, by apply vrel.map.simple; apply F,
  exp.eq_of_map X eX ▸ exp.eq_of_map Y eY ▸
    map (vset.prop_subset_refl X) (vset.prop_subset_refl Y) F' H

end /- section -/ --------------------------------------------------------------

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie ------------------------------------------------------
