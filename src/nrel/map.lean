/-

This file contains declarations for mapping one `nrel` to another.

-/

import .update
import data.exists.extra

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

namespace alpha

namespace nrel

section
variables {X₁ Y₁ X₂ Y₂ : finset V}

-- The general type of a function that maps the member names of one `nrel` to
-- another.
@[reducible]
protected
def map (R : X₁ ×ν Y₁) (S : X₂ ×ν Y₂) :=
  ∀ {x : ν∈ X₁} {y : ν∈ Y₁}, ⟪x, y⟫ ∈ν R
  → ∃ (px : x.1 ∈ X₂) (py : y.1 ∈ Y₂)
  , ⟪name.map_of_mem x px, name.map_of_mem y py⟫ ∈ν S

-- Notation for `map`.
infixr `nrel⇒`:30 := nrel.map

end

section

variables {X₁ Y₁ X₂ Y₂ : finset V}
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂}

-- Lift a `map` over `nrel.update`.
protected
theorem map.update (a b : V) : R nrel⇒ S → R ⩁ (a, b) nrel⇒ S ⩁ (a, b) :=
  begin
    intros F x y x_update_R_y,
    cases x_update_R_y with H H,
    begin
      cases H with x_eq_a y_eq_b,
      existsi name.replace_constraint_of_eq x_eq_a,
      existsi name.replace_constraint_of_eq y_eq_b,
      left, split, exact x_eq_a, exact y_eq_b
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b x_R_y,
      cases F x_R_y with px H,
      cases H with py x_S_y,
      existsi name.insert_constraint px,
      existsi name.insert_constraint py,
      right, existsi x_ne_a, existsi y_ne_b, exact x_S_y
    end
  end

end

section

variables {X Y : finset V}
variables {R S : X ×ν Y}

-- Lift a simpler function on `nrel` membership to a `map`.
protected
theorem map.simple
: (∀ {x : ν∈ X} {y : ν∈ Y}, ⟪x, y⟫ ∈ν R → ⟪x, y⟫ ∈ν S) → R nrel⇒ S :=
  λ F x y x_R_y, exists.intro₂ x.2 y.2 (by cases x; cases y; exact F x_R_y)

end

end nrel

end alpha
