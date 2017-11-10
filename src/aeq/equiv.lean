/-

This file contains equivalence properties of `aeq`.

-/

import .map

namespace acie ------------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y Z : vs V} -- Variable name sets
variables {R : X ×ν Y} {S : Y ×ν Z} -- Variable name set relations
variables {eX : exp X} {eY eY₁ eY₂ : exp Y} {eZ : exp Z} -- Expressions

-- Reflexivity
-- Paper: Proposition 2.1
protected
theorem refl (e : exp X) : e ≡α⟨vrel.id X⟩ e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r,
    begin /- var -/
      exact var (vrel.refl x)
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam (map.simple (λ x y, vrel.update.of_id) r)
    end
  end

-- Symmetry
-- Paper: Proposition 2.2
protected
theorem symm : eX ≡α⟨R⟩ eY → eY ≡α⟨R⁻¹⟩ eX :=
  begin
    intro H,
    induction H with
      /- var -/ X Y R x y x_R_y
      /- app -/ X Y R fX eX fY eY af ae rf re
      /- lam -/ X Y R a b eX eY ae r,
    begin /- var -/
      exact var (vrel.symm x_R_y)
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam (map.simple (λ x y, vrel.update.of_inv) r)
    end
  end

-- Transitivity implementation
private
theorem trans.core (P : eY₁ = eY₂) (aR : eX ≡α⟨R⟩ eY₁) (aS : eY₂ ≡α⟨S⟩ eZ)
: eX ≡α⟨R ⨾ S⟩ eZ :=
  begin
    induction aR with
      /- var -/ X Y R x y₁ x_R_y₁
      /- app -/ X Y R fX eX fY₁ eY₁ afXY aeXY rf re
      /- lam -/ X Y R x y₁ eX eY₁ aXY r
      generalizing Z S eY₂ eZ P aS,

    begin /- aR: var -/
      cases aS with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- aS: var -/
        injection P with y₁_eq_y₂ _,
        induction y₁_eq_y₂,
        exact var (vrel.trans x_R_y₁ y₂_S_z)
      end,
      begin /- aS: app -/
        exact exp.no_confusion P
      end,
      begin /- aS: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- aR: app -/
      cases aS with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- aS: var -/
        exact exp.no_confusion P
      end,
      begin /- aS: app -/
        injection P with fY₁_eq_fY₂ eY₁_eq_eY₂,
        exact app (rf fY₁_eq_fY₂ afYZ) (re eY₁_eq_eY₂ aeYZ)
      end,
      begin /- aS: lam -/
        exact exp.no_confusion P
      end
    end,

    begin /- aR: lam -/
      cases aS with
        /- var -/ Y Z S y₂ z y₂_S_z
        /- app -/ Y Z S fY₂ eY₂ fZ eZ afYZ aeYZ
        /- lam -/ Y Z S y₂ z eY₂ eZ aYZ,
      begin /- aS: var -/
        exact exp.no_confusion P
      end,
      begin /- aS: app -/
        exact exp.no_confusion P
      end,
      begin /- aS: lam -/
        injection P with y₁_eq_y₂ eY₁_heq_eY₂,
        induction y₁_eq_y₂,
        exact lam
          (map.simple (λ x z, vrel.update.of_comp)
                      (r (eq_of_heq eY₁_heq_eY₂) aYZ))
      end
    end

  end

-- Transitivity
-- Paper: Proposition 2.3
protected
theorem trans : eX ≡α⟨R⟩ eY → eY ≡α⟨S⟩ eZ → eX ≡α⟨R ⨾ S⟩ eZ :=
  trans.core (eq.refl eY)

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
