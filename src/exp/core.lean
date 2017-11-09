/-

This files contains a collection of core definitions and properties for `exp`.

-/

import .type

namespace acie ----------------------------------------------------------------
namespace exp ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

-- The `map` implementation.
def map_core (e : exp X) : ∀ {Y : vs V}, X ⊆ Y → exp Y :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r,
    begin /- var -/
      intros Y P,
      exact var (vname.map_of_subset P x)
    end,
    begin /- app -/
      intros Y P,
      exact app (rf P) (re P)
    end,
    begin /- lam -/
      intros Y P,
      exact lam (r $ vset.prop_insert_of_subset x P)
    end
  end

-- Given proof `P : X ⊆ Y`, `map P e₁ : exp Y` maps the free variables
-- from `X` to `Y` in `e₁ : exp X`.
def map : X ⊆ Y → exp X → exp Y :=
  λ P e, map_core e P

-- The identity property of `map`.
theorem eq_of_map (X : vs V) (e : exp X)
: map (vset.prop_subset_refl X) e = e :=
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
def insert_var (a : V) : exp X → exp (insert a X) :=
  map (vset.prop_subset_insert_self _ _)

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie ------------------------------------------------------
