/-

This file contains declarations related to `aeq` composition.

-/

import .map

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

namespace aeq

variables {X Y Z : finset V}
variables {R : X ×ν Y}
variables {eX : exp X} {eY₁ eY₂ : exp Y}

-- The `comp` implementation for `aeq`: composition of two `aeq`s.
def comp_core (HXY : eX ≡α⟨R⟩ eY₁)
: ∀ {Z : finset V} {S : Y ×ν Z} {eY₂ : exp Y} {eZ : exp Z}
, eY₁ = eY₂ → eY₂ ≡α⟨S⟩ eZ → eX ≡α⟨R ⨾ S⟩ eZ :=

  begin
    induction HXY with
      /- var -/ X Y R x y₁ x_R_y₁
      /- app -/ X Y R fX eX fY₁ eY₁ afXY aeXY rf re
      /- lam -/ X Y R x y₁ eX eY₁ aXY r,

    begin /- HXY: var -/
      intros Z S eY₂ eZ P HYZ,
      cases HYZ with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- HYZ: var -/
        injection P with y₁_eq_y₂ _,
        induction y₁_eq_y₂,
        exact var (nrel.trans x_R_y₁ y₂_S_z)
      end,
      begin /- HYZ: app -/
        exact exp.no_confusion P
      end,
      begin /- HYZ: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- HXY: app -/
      intros Z S p_eY' p_e₃ P HYZ,
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
      intros Z S p_e₂' p_e₃ P HYZ,
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
        exact lam
          (map_simple (λ x z, nrel.update.of_comp)
                      (r (eq_of_heq eY₁_heq_eY₂) aYZ))
      end
    end

  end

variables {S : Y ×ν Z}
variables {eY : exp Y} {eZ : exp Z}

-- A more convenient wrapper for the `comp` implementation.
def comp : eX ≡α⟨R⟩ eY → eY ≡α⟨S⟩ eZ → eX ≡α⟨R ⨾ S⟩ eZ :=
  λ aR, comp_core aR (eq.refl eY)

-- Notation for `comp`.
-- Source: http://www.fileformat.info/info/unicode/char/2a3e/index.htm
infixr ` ⨾ `:60 := comp

end aeq

end alpha
