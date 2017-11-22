/-

This files contains a collection of core definitions and properties for `exp`.

-/

import .type

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y Z : vs V} -- Variable name sets
variables {p : X ⊆ Y} {q : Y ⊆ Z} -- Subset properties

-- Given proof `p : X ⊆ Y`, `map p e` maps the free variables from `X` to `Y` in
-- `e : exp X`.
def map : X ⊆ Y → exp X → exp Y :=
  begin
    intros p e,
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r
      generalizing Y p,
    begin /- var -/
      exact var (vname.map_of_subset p x)
    end,
    begin /- app -/
      exact app (rf p) (re p)
    end,
    begin /- lam -/
      exact lam (r $ vset.prop_insert_of_subset x p)
    end
  end

namespace map ------------------------------------------------------------------

-- Identity of `map`.
theorem id (e : exp X) : map (vset.prop_subset_refl X) e = e :=
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

/-
Useful equalities for targeted rewriting.
-/

theorem of_var (x : ν∈ X)
: map p (var x) = var (vname.map_of_subset p x) :=
  rfl

theorem of_app (f e : exp X)
: map p (app f e) = app (map p f) (map p e) :=
  rfl

theorem of_lam (e : exp (insert a X))
: map p (lam e) = lam (map (vset.prop_insert_of_subset a p) e) :=
  rfl

-- Composition of `map`.
theorem comp (e : exp X)
: map q (map p e) = map (vset.prop_subset_trans p q) e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X x e r
      generalizing Y Z p q,
    begin /- var -/
      repeat {rw [map.of_var]}
    end,
    begin /- app -/
      repeat {rw [map.of_app]},
      rw [rf, re]
    end,
    begin /- lam -/
      repeat {rw [map.of_lam]},
      rw [r],
      reflexivity
    end
  end

end /- namespace -/ map --------------------------------------------------------

-- A weakening property that allows increasing the free variable set without
-- changing the structure of an expression.
def insert_var (a : V) : exp X → exp (insert a X) :=
  map (vset.prop_subset_insert_self a X)

namespace insert_var -----------------------------------------------------------

/-
Useful equalities for targeted rewriting.
-/

theorem of_var (x : ν∈ X)
: insert_var a (var x) = var (vname.insert a x) :=
  rfl

theorem of_app (f e : exp X)
: insert_var a (app f e) = app (insert_var a f) (insert_var a e) :=
  rfl

theorem of_lam₁ (e : exp (insert a X))
: insert_var b (lam e) = lam (map (vset.prop_insert_of_subset a (vset.prop_subset_insert_self b X)) e) :=
  rfl

theorem of_lam₂ (e : exp (insert a X))
: insert_var b (lam e) = lam (map (vset.prop_subset_of_insert_comm b a X) (insert_var b e)) :=
  begin
    unfold insert_var,
    rw [map.comp e],
    reflexivity
  end

theorem of_lam₃ (e : exp (insert a X))
: insert_var (fresh X).1 (lam e) = lam (map (vset.prop_subset_of_insert_comm (fresh X).1 a X) (insert_var (fresh X).1 e)) :=
  begin
    exact of_lam₂ e
  end

end /- namespace -/ insert_var -------------------------------------------------

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
