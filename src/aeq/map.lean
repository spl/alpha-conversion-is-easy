/-

This file contains the `aeq` `map` operation.

-/

import .type

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

variables {X Y X₁ Y₁ X₂ Y₂ : finset V}

namespace aeq

section

variables {R : X₁ ×ν Y₁} {eX : exp X₁} {eY : exp Y₁}

-- The `map` implementation for `aeq`.
lemma map_core (H : eX ≡α⟨R⟩ eY)
: ∀ {X₂ Y₂ : finset V} (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
    {S : X₂ ×ν Y₂} (F : R nrel⇒ S)
, exp.map pX eX ≡α⟨S⟩ exp.map pY eY :=
  begin
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r,
    begin /- var -/
      intros X₂ Y₂ pX pY S F,
      cases F x_R_y with _ H, cases H with _ x_S_y,
      exact var x_S_y
    end,
    begin /- app -/
      intros X₂ Y₂ pX pY S F,
      exact app (rf pX pY @F) (re pX pY @F)
    end,
    begin /- lam -/
      intros X₂ Y₂ pX pY S F,
      exact (lam $
        r (finset.insert_subset_insert pX)
          (finset.insert_subset_insert pY)
          (λ x y, nrel.map.update _ _ @F))
    end
  end

variables {S : X₂ ×ν Y₂}

-- Map alpha-equality from one variable relation, `R : X₁ ×ν Y₁`, to another,
-- `S : X₂ ×ν Y₂`, as long as `X₁ ⊆ X₂` and `Y₁ ⊆ Y₂`.
theorem map (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
: R nrel⇒ S → eX ≡α⟨R⟩ eY → exp.map pX eX ≡α⟨S⟩ exp.map pY eY :=
  λ F H, map_core H pX pY @F

end

section

variables {R S : X ×ν Y} {eX : exp X} {eY : exp Y}

-- A wrapper for `map` in which the free variable sets do not change.
theorem map_simple
: (∀ {x : ν∈ X} {y : ν∈ Y}, ⟪x, y⟫ ∈ν R → ⟪x, y⟫ ∈ν S) → eX ≡α⟨R⟩ eY → eX ≡α⟨S⟩ eY :=
  assume F H,
  have F' : R nrel⇒ S, by apply nrel.map.simple; apply @F,
  exp.eq_of_map X eX ▸ exp.eq_of_map Y eY ▸
    map (finset.subset.refl X) (finset.subset.refl Y) @F' H

end

end aeq -- namespace -----------------------------------------------------------

end alpha
