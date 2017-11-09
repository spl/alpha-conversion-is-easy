/-

This file contains declarations related to `aeq` inversion.

-/

import .map

namespace alpha ----------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {R : X ×ν Y} -- Variable name set relations
variables {eX : exp X} {eY : exp Y} -- Expressions

-- Inverse of `aeq`
def inv (H : eX ≡α⟨R⟩ eY) :  eY ≡α⟨R⁻¹⟩ eX :=
  begin
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

-- Notation for `inv`.
postfix ⁻¹ := inv

-- Symmetry of `aeq`
protected
theorem symm (X : vs V) : symmetric (aeq.identity X) :=
  assume e₁ e₂,
  map.simple (λ x y, vrel.inv.of_id) ∘ inv

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ alpha ------------------------------------------------------
