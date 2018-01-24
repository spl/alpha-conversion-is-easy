/-

This file contains properties of `vrel` relations.

-/

import .identity

namespace acie -----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b c : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y Z : vs V} -- Variable name sets

section ------------------------------------------------------------------------
variables {x₁ x₂ : ν∈ X} -- Variable name set members

theorem id.of_inv : ⟪x₁, x₂⟫ ∈ν (vrel.id X)° → ⟪x₁, x₂⟫ ∈ν vrel.id X :=
  eq.symm

theorem inv.of_id : ⟪x₁, x₂⟫ ∈ν vrel.id X → ⟪x₁, x₂⟫ ∈ν (vrel.id X)° :=
  eq.symm

theorem inv_of_id_iff_id_of_inv
: ⟪x₁, x₂⟫ ∈ν (vrel.id X)° ↔ ⟪x₁, x₂⟫ ∈ν vrel.id X :=
  iff.intro id.of_inv inv.of_id

theorem id.of_comp : ⟪x₁, x₂⟫ ∈ν (vrel.id X ⨾ vrel.id X) → ⟪x₁, x₂⟫ ∈ν vrel.id X :=
  begin
    intro h,
    cases h with x h,
    exact eq.trans h.1 h.2
  end

theorem comp.of_id : ⟪x₁, x₂⟫ ∈ν vrel.id X → ⟪x₁, x₂⟫ ∈ν (vrel.id X ⨾ vrel.id X) :=
  begin
    intro h,
    induction h,
    exact ⟨x₁, ⟨rfl, rfl⟩⟩
  end

theorem comp_of_id_iff_id_of_comp
: ⟪x₁, x₂⟫ ∈ν (vrel.id X ⨾ vrel.id X) ↔ ⟪x₁, x₂⟫ ∈ν vrel.id X :=
  iff.intro id.of_comp comp.of_id

end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {x₁ x₂ : ν∈ insert a X} -- Variable name set members

theorem id.of_update : ⟪x₁, x₂⟫ ∈ν vrel.id X ⩁ (a, a) → ⟪x₁, x₂⟫ ∈ν vrel.id (insert a X) :=
  vrel.is_identity.to_id _

theorem update.of_id : ⟪x₁, x₂⟫ ∈ν vrel.id (insert a X) → ⟪x₁, x₂⟫ ∈ν vrel.id X ⩁ (a, a) :=
  vrel.is_identity.from_id _

-- Paper: Lemma 1.1
theorem update_of_id_iff_id_of_update
: ⟪x₁, x₂⟫ ∈ν vrel.id X ⩁ (a, a) ↔ ⟪x₁, x₂⟫ ∈ν vrel.id (insert a X) :=
  iff.intro id.of_update update.of_id

end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {R : X ×ν Y} {S : Y ×ν Z} -- Variable name set relations
variables {x : ν∈ insert a X} {y : ν∈ insert b Y} {z : ν∈ insert c Z} -- Variable name set members

theorem inv.of_update : ⟪y, x⟫ ∈ν R° ⩁ (b, a) → ⟪y, x⟫ ∈ν (R ⩁ (a, b))° :=
  begin
    intro H,
    cases H with H H,
    begin
      cases H with y_eq_b x_eq_a, left, split, exact x_eq_a, exact y_eq_b
    end,
    begin
      cases H with y_ne_b H, cases H with x_ne_a H,
      right,
      existsi x_ne_a,
      existsi y_ne_b,
      exact H
    end
  end

theorem update.of_inv : ⟪y, x⟫ ∈ν (R ⩁ (a, b))° → ⟪y, x⟫ ∈ν R° ⩁ (b, a) :=
  begin
    intro H,
    cases H with H H,
    begin
      cases H with x_eq_a y_eq_b, left, split, exact y_eq_b, exact x_eq_a
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b H,
      right,
      existsi y_ne_b,
      existsi x_ne_a,
      exact H
    end
  end

-- Paper: Lemma 1.2
theorem update_of_inv_iff_inv_of_update
: ⟪y, x⟫ ∈ν R° ⩁ (b, a) ↔ ⟪y, x⟫ ∈ν (R ⩁ (a, b))° :=
  iff.intro inv.of_update update.of_inv

theorem update.of_comp
: ⟪x, z⟫ ∈ν R ⩁ (a, b) ⨾ S ⩁ (b, c) → ⟪x, z⟫ ∈ν (R ⨾ S) ⩁ (a, c) :=
  begin
    intro H,
    cases H with y H, cases H with x_update_R_y y_update_S_z,
    cases x_update_R_y with H H,
    begin
      cases H with x_eq_a y_eq_b,
      cases y_update_S_z with H H,
      cases H with y_eq_b z_eq_c, left, split, exact x_eq_a, exact z_eq_c,
      cases H with y_ne_b H, contradiction
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b x_R_y,
      cases y_update_S_z with H H,
      begin
        cases H with y_eq_b z_eq_c, exact absurd y_eq_b y_ne_b
      end,
      begin
        cases H with y_ne_b H, cases H with z_ne_c x_S_y,
        right,
        existsi x_ne_a,
        existsi z_ne_c,
        existsi vname.erase y y_ne_b,
        split, exact x_R_y, exact x_S_y
      end
    end
  end

theorem comp.of_update
: b ∉ Y → ⟪x, z⟫ ∈ν (R ⨾ S) ⩁ (a, c) → ⟪x, z⟫ ∈ν R ⩁ (a, b) ⨾ S ⩁ (b, c) :=
  begin
    intros pb H,
    cases H with H H,
    begin
      cases H with x_eq_a z_eq_c,
      existsi vname.insert_self b Y,
      split,
      left, split, exact x_eq_a, reflexivity,
      left, split, reflexivity, exact z_eq_c
    end,
    begin
      cases H with x_ne_a H, cases H with z_ne_c H,
      cases H with y H, cases H with x_R_y y_S_z,
      have y_ne_b : y.1 ≠ b, from vset.prop_ne_if_mem_and_not_mem y.2 pb,
      existsi vname.insert b y,
      split,
      begin
        right, existsi x_ne_a, existsi y_ne_b,
        rw [vname.eq_of_erase_insert y y_ne_b],
        exact x_R_y
      end,
      begin
        right, existsi y_ne_b, existsi z_ne_c,
        rw [vname.eq_of_erase_insert y y_ne_b],
        exact y_S_z
      end
    end
  end

-- Paper: Lemma 1.3
theorem update_of_comp_iff_comp_of_update
: b ∉ Y → (⟪x, z⟫ ∈ν (R ⨾ S) ⩁ (a, c) ↔ ⟪x, z⟫ ∈ν R ⩁ (a, b) ⨾ S ⩁ (b, c)) :=
  λ pb, iff.intro (comp.of_update pb) update.of_comp

end /- section -/ --------------------------------------------------------------

namespace update ---------------------------------------------------------------
variables {a₁ a₂ : V} -- Variable names
variables {x₁ : ν∈ insert a₁ X} {x₂ : ν∈ insert a₂ X} -- Variable name set members

theorem comp.of_id
: ⟪x₁, x₂⟫ ∈ν vrel.id X ⩁ (a₁, a₂) → ⟪x₁, x₂⟫ ∈ν (vrel.id X ⨾ vrel.id X) ⩁ (a₁, a₂) :=
  update.map (λ x₁ x₂, comp.of_id)

theorem id.of_comp
: ⟪x₁, x₂⟫ ∈ν (vrel.id X ⨾ vrel.id X) ⩁ (a₁, a₂) → ⟪x₁, x₂⟫ ∈ν vrel.id X ⩁ (a₁, a₂) :=
  update.map (λ x₁ x₂, id.of_comp)

end /- namespace -/ update -----------------------------------------------------

end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
