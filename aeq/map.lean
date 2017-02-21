/-

This file contains the `aeq` `map` operation.

-/

import .type

open [notation] eq.ops
open [notation] finset
open [notation] function
open [notation] sigma.ops
open [notation] nrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace aeq -- ===============================================================

variables {X₁ Y₁ : finset V} {R : nrel X₁ Y₁} {eX : exp X₁} {eY : exp Y₁}

-- The `map` implementation for `aeq`.
lemma map_core (H : aeq R eX eY)
: ∀ {X₂ Y₂ : finset V} (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
    {S : nrel X₂ Y₂} (F : nrel.translate R S)
, aeq S (exp.map pX eX) (exp.map pY eY) :=

  begin
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r,
    begin /- var -/
      intro X₂ Y₂ pX pY S F,
      cases F x_R_y with _ H, cases H with _ x_S_y,
      exact var x_S_y
    end,
    begin /- app -/
      intro X₂ Y₂ pX pY S F,
      exact app (rf pX pY @F) (re pX pY @F)
    end,
    begin /- lam -/
      intro X₂ Y₂ pX pY S F,
      exact lam $
        r (finset.insert_subset_insert x pX)
          (finset.insert_subset_insert y pY)
          (λ x y, nrel.translate_update @F)
    end
  end

variables {X₂ Y₂ : finset V} {S : nrel X₂ Y₂}

-- Map alpha-equality from one variable relation, `R : nrel X₁ Y₁`, to another,
-- `S : nrel X₂ Y₂`, as long as `X₁ ⊆ X₂` and `Y₁ ⊆ Y₂`.
theorem map (pX : X₁ ⊆ X₂) (pY : Y₁ ⊆ Y₂)
: nrel.translate R S → aeq R eX eY → aeq S (exp.map pX eX) (exp.map pY eY) :=

  λ F H, map_core H pX pY @F

end aeq -- namespace -----------------------------------------------------------

namespace aeq -- ===============================================================

variables {X Y : finset V} {R S : nrel X Y} {eX : exp X} {eY : exp Y}

-- A wrapper for `map` in which the free variable sets do not change.
theorem map_simple
: (∀ {x : ν∈ X} {y : ν∈ Y}, ⟪x, y, R⟫ → ⟪x, y, S⟫) → aeq R eX eY → aeq S eX eY :=

  assume F H,
  have F' : nrel.translate R S, by apply nrel.translate_simple; apply @F,
  exp.eq_of_map X eX ▸ exp.eq_of_map Y eY ▸
    map (finset.subset.refl X) (finset.subset.refl Y) @F' H

end aeq -- namespace -----------------------------------------------------------
