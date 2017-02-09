/-

This file contains `aeq` core operations and properties.

-/

import .map

open [notation] function
open [notation] vrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X`, `Y`, and `Z` are finite sets of variable names.
variables {X Y Z : finset V}

namespace aeq -- ===============================================================
-- Core operations

-- Identity of one expression
definition id (e : exp X) : aeq (vrel.id X) e e :=

  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      exact var $ eq.refl x
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam $ map_simple (λ x y, vrel.mem_update_id_of_mem_id_insert) r
    end
  end

variables {R : vrel X Y} {eX : exp X} {eY : exp Y}

-- Inverse of `aeq`
definition inverse (H : aeq R eX eY) : aeq (vrel.inverse R) eY eX :=

  begin
    induction H with
      /- var -/ X Y R x y x_R_y
      /- app -/ X Y R fX eX fY eY af ae rf re
      /- lam -/ X Y R x y eX eY a r,
    begin /- var -/
      exact var $ iff.elim_left vrel.mem_inverse_iff_mem x_R_y
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam $
        map_simple (λ x y, vrel.mem_update_inverse_of_mem_inverse_update) r
    end
  end

variables {eY₁ : exp Y}

-- The `compose` implementation for `aeq`: composition of two `aeq`s.
definition compose_core (HXY : aeq R eX eY₁)
: ∀ {Z : finset V} {S : vrel Y Z} {eY₂ : exp Y} {eZ : exp Z}
, eY₁ = eY₂ →  aeq S eY₂ eZ → aeq (R ⨾ S) eX eZ :=

  begin
    induction HXY with
      /- var -/ X Y R x y₁ x_R_y₁
      /- app -/ X Y R fX eX fY₁ eY₁ afXY aeXY rf re
      /- lam -/ X Y R x y₁ eX eY₁ aXY r,

    begin /- HXY: var -/
      intro Z S eY₂ eZ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        injection P with y₁_eq_y₂ _,
        induction y₁_eq_y₂,
        exact var $ vrel.mem_compose x_R_y₁ y₂_S_z
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
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: app -/
        injection P with fY₁_eq_fY₂ eY₁_eq_eY₂,
        exact app (rf fY₁_eq_fY₂ afYZ) (re eY₁_eq_eY₂ aeYZ)
      end,
      begin /- HYZ: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- HXY: lam -/
      intro Z S p_e₂' p_e₃ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: app -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: lam -/
        injection P with y₁_eq_y₂ eY₁_heq_eY₂,
        induction y₁_eq_y₂,
        exact lam $
          map_simple (λ x z, vrel.mem_update_compose_of_mem_compose_update)
                     (r (eq_of_heq eY₁_heq_eY₂) aYZ),
      end
    end

  end

variables {S : vrel Y Z} {eZ : exp Z}

-- A more convenient wrapper for the `compose` implementation.
definition compose : aeq R eX eY → aeq S eY eZ → aeq (R ⨾ S) eX eZ :=
  λ aR, compose_core aR (eq.refl eY)

end aeq -- namespace -----------------------------------------------------------

namespace aeq -- ===============================================================
-- Properties of `aeq (id X)`.

-- Reflexivity
theorem refl : reflexive (aeq (vrel.id X)) :=
  aeq.id

-- Symmetricity
theorem symm : symmetric (aeq (vrel.id X)) :=
  assume e₁ e₂,
  map_simple (λ x y, iff.elim_right vrel.mem_inverse_id_iff_mem_id) ∘ inverse

-- Transitivity
theorem trans : transitive (aeq (vrel.id X)) :=
  assume e₁ e₂ e₃ a₁ a₂,
  map_simple (λ x y, iff.elim_left vrel.mem_id_of_mem_compose_id) $ compose a₁ a₂

-- Equivalence
theorem equiv : equivalence (aeq (vrel.id X)) :=
  mk_equivalence (aeq (vrel.id X)) refl symm trans

end aeq -- namespace -----------------------------------------------------------
