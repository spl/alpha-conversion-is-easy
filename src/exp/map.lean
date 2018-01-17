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
def map : ∀ {X Y : vs V}, X ⊆ Y → exp X → exp Y
  | X Y p (var x)              := var (vname.map_of_subset p x)
  | X Y p (app f e)            := app (map p f) (map p e)
  | X Y p (@lam _ _ _ _ _ a e) := lam (map (vset.prop_insert_of_subset a p) e)

namespace map ------------------------------------------------------------------

-- Identity of `map`.
theorem id : ∀ {X : vs V} (e : exp X), e = map (vset.prop_subset_refl X) e
  | X (var x)   := by cases x; reflexivity
  | X (app f e) := by rw map; conv {to_lhs, rw [id f, id e]}
  | X (lam e)   := by rw map; conv {to_lhs, rw [id e]}; reflexivity

-- Composition of `map`.
theorem comp : ∀ {X Y Z : vs V} {p : X ⊆ Y} {q : Y ⊆ Z} (e : exp X),
map q (map p e) = map (vset.prop_subset_trans p q) e
  | X Y Z p q (var x)   := by repeat {rw [map]}
  | X Y Z p q (app f e) := by repeat {rw [map]}; rw [comp f, comp e]
  | X Y Z p q (lam e)   := by repeat {rw [map]}; rw [comp e]; reflexivity

end /- namespace -/ map --------------------------------------------------------

-- A weakening property that allows increasing the free variable set without
-- changing the structure of an expression.
def insert_var (a : V) : exp X → exp (insert a X) :=
  map (vset.prop_subset_insert_self a X)

namespace insert_var -----------------------------------------------------------

/- Equational lemmas -/

protected
theorem var {x : ν∈ X} : insert_var a (var x) = var (vname.insert a x) :=
  rfl

protected
theorem app {f e : exp X}
: insert_var a (app f e) = app (insert_var a f) (insert_var a e) :=
  rfl

protected
theorem lam {e : exp (insert a X)}
: insert_var b (lam e) = lam (map (vset.prop_insert_of_subset a (vset.prop_subset_insert_self b X)) e) :=
  rfl

theorem lam_comp (e : exp (insert a X))
: insert_var b (lam e) = lam (map (vset.prop_subset_of_insert_comm b a X) (insert_var b e)) :=
  by unfold insert_var; rw [map.comp e]; reflexivity

/-
protected
theorem id (e : exp (insert a X)) : insert_var a e = e :=
  begin
  end
-/

end /- namespace -/ insert_var -------------------------------------------------

end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
