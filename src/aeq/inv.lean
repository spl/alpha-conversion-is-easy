/-

This file contains declarations related to `aeq` inversion.

-/

import .map

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

namespace aeq

variables {X Y : finset V}
variables {R : X ×ν Y}
variables {eX : exp X} {eY : exp Y}

-- Inverse of `aeq`
def inv (H : eX ≡α⟨R⟩ eY) :  eY ≡α⟨R⁻¹⟩ eX :=
  begin
    induction H with
      /- var -/ X Y R x y x_R_y
      /- app -/ X Y R fX eX fY eY af ae rf re
      /- lam -/ X Y R a b eX eY ae r,
    begin /- var -/
      exact var (nrel.symm x_R_y)
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam (map_simple (λ x y, nrel.update.of_inv) r)
    end
  end

-- Notation for `inv`.
postfix ⁻¹ := inv

-- Symmetry of `aeq`
protected
theorem symm (X : finset V) : symmetric (aeq.identity X) :=
  assume e₁ e₂,
  map_simple (λ x y, nrel.inv.of_id) ∘ inv

end aeq

end alpha
