/-

This file contains definitions and theorems of combined `nrel` relations.

-/


import .identity

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X Y Z : finset V}

variables {a b c : V}

namespace alpha

namespace nrel

section
variables {x₁ x₂ : ν∈ X}

theorem inv.of_id : ⟪x₁, x₂⟫ ∈ν nrel.id X → ⟪x₁, x₂⟫ ∈ν (nrel.id X)⁻¹ :=
  eq.symm

end

section
variables {x₁ x₂ : ν∈ insert a X}

-- Produce an update on id from an id.
theorem update.of_id : ⟪x₁, x₂⟫ ∈ν nrel.id (insert a X) → ⟪x₁, x₂⟫ ∈ν nrel.id X ⩁ (a, a) :=
  -- I'm not sure why the type class inference doesn't resolve the
  -- id.is_identity instance here.
  @is_identity.from_id _ _ _ _ (@update.is_identity _ _ _ _ (@id.is_identity _ _ X) _) _ _

end

section
variables {R : X ×ν Y}
variables {x : ν∈ insert a X} {y : ν∈ insert b Y}

theorem inv.of_update : ⟪y, x⟫ ∈ν R⁻¹ ⩁ (b, a) → ⟪y, x⟫ ∈ν (R ⩁ (a, b))⁻¹ :=
  begin
    intro H,
    cases H with H H,
    begin
      cases H, left, split, exact right, exact left
    end,
    begin
      cases H with y_ne_b H, cases H with x_ne_a H,
      right,
      existsi x_ne_a,
      existsi y_ne_b,
      exact H
    end
  end

theorem update.of_inv : ⟪y, x⟫ ∈ν (R ⩁ (a, b))⁻¹ → ⟪y, x⟫ ∈ν R⁻¹ ⩁ (b, a) :=
  begin
    intro H,
    cases H with H H,
    begin
      cases H, left, split, exact right, exact left
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b H,
      right,
      existsi y_ne_b,
      existsi x_ne_a,
      exact H
    end
  end

theorem update_of_inv_iff_inv_of_update (x : ν∈ insert a X) (y : ν∈ insert b Y)
: ⟪y, x⟫ ∈ν R⁻¹ ⩁ (b, a) ↔ ⟪y, x⟫ ∈ν (R ⩁ (a, b))⁻¹ :=
  iff.intro inv.of_update update.of_inv

end

section
variables {R : X ×ν Y} {S : Y ×ν Z}
variables {x : ν∈ insert a X} {y : ν∈ insert b Y} {z : ν∈ insert c Z}

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
        existsi name.erase y y_ne_b,
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
      existsi name.self b Y,
      split,
      left, split, exact x_eq_a, reflexivity,
      left, split, reflexivity, exact z_eq_c
    end,
    begin
      cases H with x_ne_a H, cases H with z_ne_c H,
      cases H with y H, cases H with x_R_y y_S_z,
      have y_ne_b : y.1 ≠ b, from finset.ne_of_mem_of_not_mem y.2 pb,
      existsi name.insert b y,
      split,
      begin
        right, existsi x_ne_a, existsi y_ne_b,
        rw [name.eq_of_erase_insert y y_ne_b],
        exact x_R_y
      end,
      begin
        right, existsi y_ne_b, existsi z_ne_c,
        rw [name.eq_of_erase_insert y y_ne_b],
        exact y_S_z
      end
    end
  end

theorem update_of_comp_iff_comp_of_update
: b ∉ Y → (⟪x, z⟫ ∈ν (R ⨾ S) ⩁ (a, c) ↔ ⟪x, z⟫ ∈ν R ⩁ (a, b) ⨾ S ⩁ (b, c)) :=
  λ pb, iff.intro (comp.of_update pb) update.of_comp

end

end nrel

end alpha
