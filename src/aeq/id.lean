/-

This file contains declarations related to `aeq` identity or reflexivity.

-/

import .map

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X : finset V}

namespace alpha

namespace aeq

-- Identity of one expression
protected
def id (e : exp X) : e ≡α e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r,
    begin /- var -/
      exact var (nrel.refl x)
    end,
    begin /- app -/
      exact app rf re
    end,
    begin /- lam -/
      exact lam (map_simple (λ x y, nrel.update.of_id) r)
    end
  end

-- Reflexivity
protected
theorem refl (X : finset V) : reflexive (aeq.identity X) :=
  aeq.id

end aeq

end alpha
