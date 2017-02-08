/-

This file contains `aeq` core operations and properties.

-/

import .map

open function
open vrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X`, `Y`, and `Z` consistently refer to finite sets of variable names.
variables {X Y Z : finset V}

-- Disambiguate `vrel.id` from `aeq.id`.
local abbreviation id' : ∀ X : finset V, vrel X X := vrel.id

namespace aeq -- ===============================================================
-- Core operations

-- Identity of one expression
definition id (e : exp X) : aeq (id' X) e e :=

  begin
    induction e with
      /- var -/ X x px
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      exact var $ mem_id px
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam $ map_simple (λ c d pc pd, mem_update_id_of_mem_id_insert) r
    end
  end

variables {R : vrel X Y} {eX : exp X} {eY : exp Y}

-- Inverse of `aeq`
definition inverse (H : aeq R eX eY) : aeq (inverse R) eY eX :=

  begin
    induction H with
      /- var -/ X Y R x y px py x_R_y
      /- app -/ X Y R fX eX fY eY af ae rf re
      /- lam -/ X Y R x y eX eY a r,
    begin /- var -/
      exact var $ iff.elim_left mem_inverse_iff_mem x_R_y
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam $
        map_simple (λ c d pc pd, mem_update_inverse_of_mem_inverse_update) r
    end
  end

variables {eY₁ : exp Y}

-- The `compose` implementation for `aeq`: composition of two `aeq`s.
definition compose_core (HXY : aeq R eX eY₁)
: ∀ {Z : finset V} {S : vrel Y Z} {eY₂ : exp Y} {eZ : exp Z}
, eY₁ = eY₂ →  aeq S eY₂ eZ → aeq (R ⨾ S) eX eZ :=

  begin
    induction HXY with
      /- var -/ X Y R x y₁ px py₁ x_R_y₁
      /- app -/ X Y R fX eX fY₁ eY₁ afXY aeXY rf re
      /- lam -/ X Y R x y₁ eX eY₁ aXY r,

    begin /- HXY: var -/
      intro Z S eY₂ eZ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z px py y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        have y₁_eq_y₂ : y₁ = y₂, from exp.no_confusion P $ λ P₁ P₂ P₃, P₂,
        induction y₁_eq_y₂,
        exact var $ mem_compose x_R_y₁ y₂_S_z
      end,
      begin /- HYZ: app -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- HXY: app -/
      intro Z S p_eY' p_e₃ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z px py y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: app -/
        have fY₁_eq_fY₂ : fY₁ = fY₂, from
          eq_of_heq $ exp.no_confusion P $ λ P₁ P₂ P₃, P₂,
        have eY₁_eq_eY₂ : eY₁ = eY₂, from
          eq_of_heq $ exp.no_confusion P $ λ P₁ P₂ P₃, P₃,
        exact app (rf fY₁_eq_fY₂ afYZ) (re eY₁_eq_eY₂ aeYZ)
      end,
      begin /- HYZ: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- HXY: lam -/
      intro Z S p_e₂' p_e₃ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z px py y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: app -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: lam -/
        have y₁_eq_y₂ : y₁ = y₂, from exp.no_confusion P $ λ P₁ P₂ P₃, P₂,
        induction y₁_eq_y₂,
        have eY₁_eq_eY₂ : eY₁ = eY₂, from
          eq_of_heq $ exp.no_confusion P $ λ P₁ P₂ P₃, P₃,
        exact lam $
          map_simple (λ c d pc pd, mem_update_compose_of_mem_compose_update)
                     (r eY₁_eq_eY₂ aYZ),
      end
    end

  end

variables {S : vrel Y Z} {eZ : exp Z}

-- A more convenient wrapper for the `compose` implementation.
definition compose (aR : aeq R eX eY) (aS : aeq S eY eZ) : aeq (R ⨾ S) eX eZ :=
  @compose_core _ _ X Y R eX eY aR Z S eY eZ rfl aS

end aeq -- namespace -----------------------------------------------------------

namespace aeq -- ===============================================================
-- Properties of the identity `aeq`, `aeq (id X)`.

variables {e e₁ e₂ e₃ : exp X}

-- Reflexivity
theorem reflexive : aeq (id' X) e e := aeq.id e

-- Symmetricity
theorem symmetric (a : aeq (id' X) e₁ e₂) : aeq (id' X) e₂ e₁ :=
  map_simple (λ c d pc pd, iff.elim_right mem_inverse_id_iff_mem_id)
             (inverse a)

-- Transitivity
theorem transitive (a₁ : aeq (id' X) e₁ e₂) (a₂ : aeq (id' X) e₂ e₃)
: aeq (id' X) e₁ e₃ :=
  map_simple (λ c d pc pd, iff.elim_left mem_id_of_mem_compose_id)
             (compose a₁ a₂)

end aeq -- namespace -----------------------------------------------------------
