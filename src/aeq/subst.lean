/-

This file contains the proof that substitution preserves alpha equality.

-/

import .map

namespace alpha

namespace aeq -- ===============================================================

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X X₁ X₂ Y Y₁ Y₂ Z : vs V} -- Variable name sets
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂} -- Variable name set relations
variables {F : exp.subst X₁ X₂} {G : exp.subst Y₁ Y₂} -- Substitutions

-- This is the type of a function that lifts a relation `R` to an alpha-equality
-- relation on `S` with the substitutions `F` and `G` applied to each side.
def subst_aeq
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
(R : X₁ ×ν Y₁) (S : X₂ ×ν Y₂) :=
  ∀ {x : ν∈ X₁} {y : ν∈ Y₁}, ⟪x, y⟫ ∈ν R → F x ≡α⟨S⟩ G y

-- A lemma needed for the `lam` case in `subst_preservation_core`.
lemma subst_preservation_update (nx₂ : ν∉ X₂) (ny₂ : ν∉ Y₂)
: subst_aeq F G R S
→ subst_aeq
    (exp.subst_update_var a nx₂.1 F)
    (exp.subst_update_var b ny₂.1 G)
    (vrel.update a b R)
    (vrel.update nx₂.1 ny₂.1 S) :=

  begin
    intros P x₁ y₁ H,
    cases H with H H,
    begin
      cases H with x₁_eq_a y₁_eq_b,
      unfold exp.subst_update_var exp.subst_update,
      rw [dif_pos x₁_eq_a, dif_pos y₁_eq_b],
      apply var, left, split, reflexivity, reflexivity
    end,
    begin
      cases H with x₁_ne_a₁ H,
      cases H with y₁_ne_b₁ x₁_R_y₁,
      unfold exp.subst_update_var exp.subst_update,
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
        exact P x₁_R_y₁
      end
    end
  end

section
variables {eX₁ : exp X₁} {eY₁ : exp Y₁} -- Expressions

-- The implementation of `subst_preservation`.
def subst_preservation_core (H : eX₁ ≡α⟨R⟩ eY₁)
: ∀ {X₂ Y₂ : vs V} {S : X₂ ×ν Y₂}
    (F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
    (P : subst_aeq F G R S)
, exp.subst_apply F eX₁ ≡α⟨S⟩ exp.subst_apply G eY₁ :=
  begin
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r,
    begin /- var -/
      intros X₂ Y₂ S F G P,
      exact P x_R_y
    end,
    begin /- app -/
      intros X₂ Y₂ S F G P,
      exact app (rf F G @P) (re F G @P)
    end,
    begin /- lam -/
      intros X₂ Y₂ S F G P,
      apply lam,
      exact r
        (exp.subst_update_var x (fresh X₂).1 F)
        (exp.subst_update_var y (fresh Y₂).1 G)
        (λ x y, subst_preservation_update (fresh X₂) (fresh Y₂) @P)
    end
  end

-- General form of substitution preserves alpha equality property.
def subst_preservation_general
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
: subst_aeq F G R S
→ eX₁ ≡α⟨R⟩ eY₁
→ exp.subst_apply F eX₁ ≡α⟨S⟩ exp.subst_apply G eY₁ :=
  λ P H, subst_preservation_core H F G @P

end

section
variables {eX₁ eX₂ : exp X} -- Expressions

-- Substitution preserves alpha equality.
def subst_preservation
(F : exp.subst X Y) (G : exp.subst X Y)
: subst_aeq F G (vrel.id X) (vrel.id Y)
→ eX₁ ≡α eX₂
→ exp.subst_apply F eX₁ ≡α exp.subst_apply G eX₂ :=
  subst_preservation_general F G

end

theorem self_aeq_subst_apply_lift (e : exp X)
: ∀ {Y : vs V} (F : X →ν Y)
, e ≡α⟨vrel.lift F⟩ exp.subst_apply (exp.subst.lift F) e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r,
    begin /- var -/
      intros Y F,
      exact var rfl
    end,
    begin /- app -/
      intros Y F,
      exact app (rf F) (re F)
    end,
    begin /- lam -/
      intros Y F,
      have H : e ≡α⟨vrel.lift (vname.update a (fresh Y).1 F)⟩ exp.subst_apply (exp.subst.lift (vname.update a (fresh Y).1 F)) e :=
        r (vname.update a (fresh Y).1 F),
      have P : exp.subst_update_var a (fresh Y).1 (exp.subst.lift F) = exp.subst.lift (vname.update a (fresh Y).1 F) :=
        funext (exp.subst_update_var_eq_var_update a (fresh Y).1 F),
      rw [←P] at H,
      exact (lam (map.simple vrel.update.lift H))
    end
  end

end aeq -- namespace -----------------------------------------------------------

end alpha
