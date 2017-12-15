/-

This file contains the proof that substitution preserves alpha equality.

-/

import .id

namespace acie -----------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X X₁ X₂ Y Y₁ Y₂ Z : vs V} -- Variable name sets
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂} -- Variable name set relations
variables {F : exp.subst X₁ X₂} {G : exp.subst Y₁ Y₂} -- Substitutions

-- This is the type of a function that extends a variable name set relation `R`
-- to an alpha-equality relation on `S` with the substitutions `F` and `G`
-- applied to the left and right sides, respectively.
@[reducible]
protected
def extend (F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂) (R : X₁ ×ν Y₁) (S : X₂ ×ν Y₂) :=
  ∀ (x : ν∈ X₁) (y : ν∈ Y₁), ⟪x, y⟫ ∈ν R → F x ≡α⟨S⟩ G y

@[reducible]
protected
def extend.id (F : exp.subst X Y) : aeq.extend F F (vrel.id X) (vrel.id Y) :=
  λ x₁ x₂ x₁_eq_x₂, by induction x₁_eq_x₂; exact aeq.refl (F x₁)

-- A lemma needed for the `lam` case in `subst_preservation`.
-- Paper: Lemma 5
lemma subst_preservation.update (nx₂ : ν∉ X₂) (ny₂ : ν∉ Y₂)
: aeq.extend F G R S
→ aeq.extend (exp.subst.update a nx₂.1 F)
             (exp.subst.update b ny₂.1 G)
             (vrel.update a b R)
             (vrel.update nx₂.1 ny₂.1 S) :=
  begin
    intros P x₁ y₁ H,
    cases H with H H,
    begin
      cases H with x₁_eq_a y₁_eq_b,
      simp [exp.subst.update],
      rw [dif_pos x₁_eq_a, dif_pos y₁_eq_b],
      apply var, left, split, reflexivity, reflexivity
    end,
    begin
      cases H with x₁_ne_a₁ H,
      cases H with y₁_ne_b₁ x₁_R_y₁,
      simp [exp.subst.update],
      rw [dif_neg x₁_ne_a₁, dif_neg y₁_ne_b₁],
      apply map (vset.prop_subset_insert_self _ _) (vset.prop_subset_insert_self _ _),
      begin
        intros x₂ y₂ c_S_d,
        cases x₂ with x₂ px₂, cases y₂ with y₂ py₂,
        existsi vset.prop_insert nx₂.1 px₂,
        existsi vset.prop_insert ny₂.1 py₂,
        right,
        existsi vset.prop_ne_if_mem_and_not_mem px₂ nx₂.2,
        existsi vset.prop_ne_if_mem_and_not_mem py₂ ny₂.2,
        exact c_S_d
      end,
      begin
        exact P (vname.erase x₁ x₁_ne_a₁) (vname.erase y₁ y₁_ne_b₁) x₁_R_y₁
      end
    end
  end

section ------------------------------------------------------------------------
variables {eX₁ : exp X₁} {eY₁ : exp Y₁} -- Expressions

-- Substitution preserves alpha equality
-- Paper: Proposition 4
theorem subst_preservation
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
: aeq.extend F G R S
→ eX₁ ≡α⟨R⟩ eY₁
→ exp.subst.apply F eX₁ ≡α⟨S⟩ exp.subst.apply G eY₁ :=
  begin
    intros P H,
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r
      generalizing X₂ Y₂ S F G P,
    begin /- var -/
      exact P x y x_R_y
    end,
    begin /- app -/
      exact app (rf F G P) (re F G P)
    end,
    begin /- lam -/
      apply lam,
      exact r
        (exp.subst.update x (fresh X₂).1 F)
        (exp.subst.update y (fresh Y₂).1 G)
        (subst_preservation.update (fresh X₂) (fresh Y₂) P)
    end
  end

end /- section -/ --------------------------------------------------------------

section ------------------------------------------------------------------------
variables {eX₁ eX₂ : exp X} -- Expressions

-- Substitution preservation with the identity relation.
protected
theorem subst_preservation.id
(F : exp.subst X Y) (G : exp.subst X Y)
: aeq.extend F G (vrel.id X) (vrel.id Y)
→ eX₁ ≡α eX₂
→ exp.subst.apply F eX₁ ≡α exp.subst.apply G eX₂ :=
  subst_preservation F G

-- Substitution preservation with the identity relation and one substitution.
protected
theorem subst_preservation.id₁
(F : exp.subst X Y)
: eX₁ ≡α eX₂
→ exp.subst.apply F eX₁ ≡α exp.subst.apply F eX₂ :=
  aeq.subst_preservation.id F F (aeq.extend.id F)

end /- section -/ --------------------------------------------------------------

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
