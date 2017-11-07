/-

This files contains a collection of core definitions and properties for `exp`.

-/

import .type

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X` and `Y` are finite sets of variable names.
variables {X Y : finset V}

namespace alpha

namespace exp -- ===============================================================
-- The `exp` `map` operation.

-- The `map` implementation.
definition map_core (e : exp X) : ∀ {Y : finset V}, X ⊆ Y → exp Y :=

  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      intros Y P,
      exact var (name.map_of_subset P x)
    end,
    begin /- app -/
      intros Y P,
      exact app (rf P) (re P)
    end,
    begin /- lam -/
      intros Y P,
      exact lam (r $ finset.insert_subset_insert P)
    end
  end

-- Given proof `P : X ⊆ Y`, `map P e₁ : exp Y` maps the free variables
-- from `X` to `Y` in `e₁ : exp X`.
definition map : X ⊆ Y → exp X → exp Y :=
  λ P e, map_core e P

-- The identity property of `map`.
theorem eq_of_map (X : finset V) (e : exp X)
: map (finset.subset.refl X) e = e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X e₁ e₂ r₁ r₂
      /- lam -/ X x e r,
    begin /- var -/
      cases x,
      reflexivity
    end,
    begin /- app -/
      conv {to_rhs, rw [←r₁, ←r₂]},
      reflexivity
    end,
    begin /- lam -/
      conv {to_rhs, rw [←r]},
      reflexivity
    end
  end

-- A weakening property that allows increasing the free variable set without
-- changing the structure of an expression.
definition insert_var (a : V) : exp X → exp (insert a X) :=
  map finset.subset_insert

end exp -- namespace -----------------------------------------------------------

end alpha
