/-

This file contains declarations related to `aeq` identity or reflexivity.

-/

import .map

namespace alpha

namespace aeq

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets

-- Identity of one expression
protected
def id (e : exp X) : e ≡α e :=
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

-- Reflexivity
protected
theorem refl (X : vs V) : reflexive (aeq.identity X) :=
  aeq.id

end aeq

end alpha
