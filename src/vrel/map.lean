/-

This file contains declarations for mapping one `vrel` to another.

-/

import .update

namespace acie -----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X X₁ X₂ Y Y₁ Y₂ : vs V} -- Variable name sets

-- The type of a function that maps over the sets of a `vrel`.
@[reducible]
protected
def map (R : X₁ ×ν Y₁) (S : X₂ ×ν Y₂) :=
  ∀ (x : ν∈ X₁) (y : ν∈ Y₁), ⟪x, y⟫ ∈ν R
  → ∃ (px : x.1 ∈ X₂) (py : y.1 ∈ Y₂)
  , ⟪vname.map_of_mem x px, vname.map_of_mem y py⟫ ∈ν S

-- Notation for `map`.
infixr ` ⇒ν `:30 := vrel.map

namespace map ------------------------------------------------------------------

section ------------------------------------------------------------------------
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂} -- Variable name set relations

-- Lift a `map` over `vrel.update`.
protected
theorem update (a b : V) : R ⇒ν S → R ⩁ (a, b) ⇒ν S ⩁ (a, b) :=
  begin
    intros F x y x_update_R_y,
    cases x_update_R_y with H H,
    begin
      cases H with x_eq_a y_eq_b,
      existsi vset.prop_insert_self_if_eq X₂ x_eq_a,
      existsi vset.prop_insert_self_if_eq Y₂ y_eq_b,
      left, split, exact x_eq_a, exact y_eq_b
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b x_R_y,
      cases F (vname.erase x x_ne_a) (vname.erase y y_ne_b) x_R_y with px H,
      cases H with py x_S_y,
      existsi vset.prop_insert a px,
      existsi vset.prop_insert b py,
      right, existsi x_ne_a, existsi y_ne_b, exact x_S_y
    end
  end

end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {R S : X ×ν Y} -- Variable name set relations

-- Lift a simpler function on `vrel` membership to a `map`.
protected
theorem simple : (∀ (x : ν∈ X) (y : ν∈ Y), ⟪x, y⟫ ∈ν R → ⟪x, y⟫ ∈ν S) → R ⇒ν S :=
  begin
    intros F x y x_R_y,
    cases x with x px, cases y with y py,
    existsi px, existsi py,
    exact F (vname.map_of_mem ⟨x, px⟩ px) (vname.map_of_mem ⟨y, py⟩ py) x_R_y
  end

end /- section -/ --------------------------------------------------------------

end /- namespace -/ map --------------------------------------------------------
end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
