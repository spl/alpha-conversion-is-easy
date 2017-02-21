/-

This file contains the `nrel` `update` operation and its properties.

-/

import .core

import data.finset.fresh

open [notation] eq.ops
open [class] [notation] finset
open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X`, `Y`, and `Z` are finite sets of variable names.
variables {X Y Z : finset V}

namespace nrel -- ==============================================================

/-
The `update` operation takes `R : nrel X Y`, erases from `R` every pair with
either `a` on the left or `b` on the right, and extends the relation with the
pair `(a, b)`.

A simple way to think about `update a b` is (using brackets for readability):

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ x ∈ X ∧ y ∈ Y ∧ R a b)

However, that does not give the proper type indexing of `R`. A closer model is:

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ R (name.erase x px) (name.erase y py))

But note that `px : a ≠ x` and `py : b ≠ y` are not available as arguments to
`R`. Therefore, we use an existentially quantified right alternative to include
these as propositions as well as their types as arguments.
-/

definition update (a b : V) : nrel X Y → nrel ('{a} ∪ X) ('{b} ∪ Y) :=
  assume (R : nrel X Y) (x : ν∈ '{a} ∪ X) (y : ν∈ '{b} ∪ Y),
  (x.1 = a ∧ y.1 = b) ∨
  (∃ (px : x.1 ≠ a) (py : y.1 ≠ b), R (name.erase x px) (name.erase y py))

end nrel -- namespace ----------------------------------------------------------

-- Global attributes
attribute nrel.update [reducible]

namespace nrel -- ==============================================================
-- Some basic properties of `update`.

variables {X₁ Y₁ X₂ Y₂ : finset V}

-- The type of a function that translates one `nrel` to another.
definition translate [reducible] (R : nrel X₁ Y₁) (S : nrel X₂ Y₂) :=
  ∀   {x : ν∈ X₁}     {y : ν∈ Y₁},     ⟪x,                    y,                    R⟫
  → ∃ (px : x.1 ∈ X₂) (py : y.1 ∈ Y₂), ⟪name.map_of_mem x px, name.map_of_mem y py, S⟫

-- Lift a simpler function on `nrel`s to a `translate`.
definition translate_simple {R S : nrel X Y}
: (∀ {x : ν∈ X} {y : ν∈ Y}, ⟪x, y, R⟫ → ⟪x, y, S⟫) → translate R S :=

  assume F x y x_R_y,
  exists.intro x.2 $ exists.intro y.2 (by cases x; cases y; exact F x_R_y)

variables {R : nrel X₁ Y₁} {S : nrel X₂ Y₂}

-- Lift a `translate` over `update`d `nrel`s.
theorem translate_update {a b : V}
: translate R S → translate (update a b R) (update a b S) :=

  begin
    intro F x y H,
    cases H with H H,
    begin
      cases H,
      existsi name.replace_constraint_of_eq X₂ x.2 `x.1 = a`,
      existsi name.replace_constraint_of_eq Y₂ y.2 `y.1 = b`,
      left, split, assumption, assumption,
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b x_R_y,
      cases F x_R_y with px H,
      cases H with py x_S_y,
      existsi name.insert_constraint a px,
      existsi name.insert_constraint b py,
      right, existsi by assumption, existsi by assumption, exact x_S_y
    end
  end

end nrel -- namespace ----------------------------------------------------------

attribute nrel.translate        [reducible]
attribute nrel.translate_simple [reducible]

namespace nrel -- ==============================================================
-- Properties of `update` and `id`.

variables {a : V}
variables {x₁ : ν∈ '{a} ∪ X} {x₂ : ν∈ '{a} ∪ X}

-- `update a a (id X) → id ('{a} ∪ X)`.
lemma mem_id_insert_of_mem_update_id
: ⟪x₁, x₂, update a a (id X)⟫ → ⟪x₁, x₂, id ('{a} ∪ X)⟫ :=

  begin
    intro H,
    cases H with H H,
    begin
      cases H with x₁_eq_a x₂_eq_a,
      apply name.eq, transitivity a, assumption, symmetry, assumption,
    end,
    begin
      cases H with x₁_ne_a H, cases H with x₂_ne_a H,
      injection H with H₁ H₂,
      apply name.eq, exact H₁
    end
  end

-- `id ('{a} ∪ X) → update a a (id X)`.
lemma mem_update_id_of_mem_id_insert
: ⟪x₁, x₂, id ('{a} ∪ X)⟫ → ⟪x₁, x₂, update a a (id X)⟫ :=

  begin
    intro H,
    unfold [id],
    cases (decidable.em (x₁.1 = a)),
    left, split, assumption, cases H, assumption,
    right, existsi by assumption, cases H, existsi by assumption, reflexivity
  end

-- Show that `update a a (id X) ↔ id ('{a} ∪ X)`.
theorem mem_update_id_iff_mem_id_insert
: ⟪x₁, x₂, update a a (id X)⟫ ↔ ⟪x₁, x₂, id ('{a} ∪ X)⟫ :=

  iff.intro mem_id_insert_of_mem_update_id
            mem_update_id_of_mem_id_insert

end nrel -- namespace ----------------------------------------------------------

namespace nrel -- ==============================================================
-- Properties of `update` and `inverse`.

variables {R : nrel X Y}
variables {a b : V}
variables {x : ν∈ '{a} ∪ X} {y : ν∈ '{b} ∪ Y}

-- `inverse (update a b R) → update b a (inverse R)`
lemma mem_update_inverse_of_mem_inverse_update
: ⟪y, x, inverse (update a b R)⟫ → ⟪y, x, update b a (inverse R)⟫ :=

  begin
    intro H,
    cases H with H H,
    begin
      cases H, left, split, assumption, assumption,
    end,
    begin
      cases H with x_ne_a H, cases H, right,
      existsi by assumption,
      existsi by assumption,
      assumption,
    end
  end

-- `update b a (inverse R) → inverse (update a b R)`
lemma mem_inverse_update_of_mem_update_inverse
: ⟪y, x, update b a (inverse R)⟫ → ⟪y, x, inverse (update a b R)⟫ :=

  begin
    intro H,
    cases H with H H,
    begin
      cases H, left, split, assumption, assumption,
    end,
    begin
      cases H with x_ne_a H, cases H, right,
      existsi by assumption,
      existsi by assumption,
      assumption
    end
  end

-- `inverse (update a b R) → update b a (inverse R)`
theorem mem_update_inverse_iff_mem_inverse_update
: ⟪y, x, inverse (update a b R)⟫ ↔ ⟪y, x, update b a (inverse R)⟫ :=

  iff.intro mem_update_inverse_of_mem_inverse_update
            mem_inverse_update_of_mem_update_inverse

end nrel -- namespace ----------------------------------------------------------

namespace nrel -- ==============================================================
-- Properties of `update` and `compose`.

variables {R : nrel X Y} {S : nrel Y Z}
variables {a b c : V}
variables {x : ν∈ '{a} ∪ X} {z : ν∈ '{c} ∪ Z}

-- `update a b R ⨾ update b c S → update a c (R ⨾ S)`
lemma mem_update_compose_of_mem_compose_update
: ⟪x, z, update a b R ⨾ update b c S⟫ → ⟪x, z, update a c (R ⨾ S)⟫ :=

  begin
    intro H,
    cases H with y H, cases H with x_update_R_y y_update_S_z,
    cases x_update_R_y with H H,
    begin
      cases H,
      cases y_update_S_z with H H,
      cases H, left, split, assumption, assumption,
      cases H, contradiction
    end,
    begin
      cases H with x_ne_a H, cases H with y_ne_b x_R_y,
      cases y_update_S_z with H H,
      begin
        cases H with y_eq_b z_eq_c, exact absurd y_eq_b y_ne_b
      end,
      begin
        cases H with x_ne_a H, cases H with y_ne_b x_S_y,
        right,
        existsi by assumption,
        existsi by assumption,
        existsi name.erase y y_ne_b,
        split, assumption, assumption
      end
    end
  end

-- `update a c (R ⨾ S) → update a b R ⨾ update b c S`
lemma mem_compose_update_of_mem_update_compose
: b ∉ Y → ⟪x, z, update a c (R ⨾ S)⟫ → ⟪x, z, update a b R ⨾ update b c S⟫ :=

  begin
    intro pb H,
    cases H with H H,
    begin
      cases H with x_eq_a z_eq_c,
      existsi ⟨b, name.self_constraint b Y⟩,
      split,
      left, split, assumption, reflexivity,
      left, split, reflexivity, assumption
    end,
    begin
      cases H with x_ne_a H, cases H with z_ne_c H,
      cases H with y H, cases H with x_R_y y_S_z,
      have y_ne_b : y.1 ≠ b, from finset.ne_of_mem_of_not_mem y.2 pb,
      existsi name.insert b y,
      split,
      begin
        right, existsi by assumption, existsi y_ne_b,
        rewrite [name.eq_of_erase_insert y y_ne_b],
        exact x_R_y
      end,
      begin
        right, existsi y_ne_b, existsi by assumption,
        rewrite [name.eq_of_erase_insert y y_ne_b],
        exact y_S_z
      end
    end
  end

-- `update a b R ⨾ update b c S ↔ update a c (R ⨾ S)`
theorem mem_update_compose_iff_mem_compose_update
: b ∉ Y → (⟪x, z, update a c (R ⨾ S)⟫ ↔ ⟪x, z, update a b R ⨾ update b c S⟫) :=

  assume pb,
  iff.intro (mem_compose_update_of_mem_update_compose pb)
            mem_update_compose_of_mem_compose_update

end nrel -- namespace ----------------------------------------------------------

namespace nrel -- ==============================================================
-- Theorems with name.update

variables [finset.has_fresh V]
variables {a : V} {F : ν∈ X → ν∈ Y}

-- Lift a `name.update` of a fresh variable to a `nrel.update`.
definition lift_update_of_fresh
(x : ν∈ '{a} ∪ X) (y : ν∈ '{(finset.fresh Y).1} ∪ Y)
: lift (name.update a (finset.fresh Y).1 F) x y
→ update a (finset.fresh Y).1 (lift F) x y :=

  begin
    cases x with x px,
    cases y with y py,
    unfold [nrel.lift, name.update],
    intro H,
    cases decidable.em (x = a) with x_eq_a x_ne_a,
    begin /- x = a -/
      rewrite [dif_pos x_eq_a at H],
      left, split, exact x_eq_a, exact H⁻¹
    end,
    begin /- x ≠ a -/
      rewrite [dif_neg x_ne_a at H],
      right,
      existsi x_ne_a,
      induction H,
      existsi name.ne_of_iname_of_oname (F (name.erase ⟨x, px⟩ x_ne_a)) (finset.fresh Y),
      reflexivity,
    end
  end

end nrel -- namespace ----------------------------------------------------------
