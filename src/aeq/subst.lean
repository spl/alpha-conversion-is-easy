/-

This file contains the proof that substitution preserves alpha equality.

-/

import .map

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `finset V` is the type of a finite set of variable names with freshness.
variables [finset.has_fresh V]

-- `X`, `Y`, and variations are finite sets of variable names.
variables {X X₁ X₂ Y Y₁ Y₂ : finset V}

namespace alpha

namespace aeq -- ===============================================================

-- This is the type of a function that lifts a relation `R` to an alpha-equality
-- relation on `S` with the substitutions `F` and `G` applied to each side.
def subst_aeq
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
(R : X₁ ×ν Y₁) (S : X₂ ×ν Y₂) :=
  ∀ {x : ν∈ X₁} {y : ν∈ Y₁}, ⟪x, y⟫ ∈ν R → F x ≡α⟨S⟩ G y

section

variables {F : exp.subst X₁ X₂} {G : exp.subst Y₁ Y₂}
variables {R : X₁ ×ν Y₁} {S : X₂ ×ν Y₂}
variables {a b : V}

-- A lemma needed for the `lam` case in `subst_preservation_core`.
lemma subst_preservation_update (nx₂ : ν∉ X₂) (ny₂ : ν∉ Y₂)
: subst_aeq F G R S
→ subst_aeq
    (exp.subst_update_var a nx₂.1 F)
    (exp.subst_update_var b ny₂.1 G)
    (nrel.update a b R)
    (nrel.update nx₂.1 ny₂.1 S) :=

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
      apply map finset.subset_insert finset.subset_insert,
      tactic.rotate 3,
      begin
        exact _inst_1
      end,
      begin
        exact _inst_1
      end,
      tactic.rotate 2,
      begin
        exact S
      end,
      tactic.rotate 1,
      begin
        exact P x₁_R_y₁
      end,
      begin
        intros x₂ y₂ c_S_d,
        cases x₂ with x₂ px₂, cases y₂ with y₂ py₂,
        existsi name.insert_constraint px₂,
        existsi name.insert_constraint py₂,
        right,
        existsi finset.ne_of_mem_of_not_mem px₂ nx₂.2,
        existsi finset.ne_of_mem_of_not_mem py₂ ny₂.2,
        exact c_S_d
      end
    end
  end

variables {eX : exp X₁} {eY : exp Y₁}

-- The implementation of `subst_preservation`.
def subst_preservation_core (H : eX ≡α⟨R⟩ eY)
: ∀ {X₂ Y₂ : finset V} {S : X₂ ×ν Y₂}
    (F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
    (P : subst_aeq F G R S)
, exp.subst_apply F eX ≡α⟨S⟩ exp.subst_apply G eY :=
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
        (exp.subst_update_var x (finset.fresh X₂).1 F)
        (exp.subst_update_var y (finset.fresh Y₂).1 G)
        (λ x y, subst_preservation_update (finset.fresh X₂) (finset.fresh Y₂) @P)
    end
  end

-- General form of substitution preserves alpha equality property.
def subst_preservation_general
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
: subst_aeq F G R S
→ eX ≡α⟨R⟩ eY
→ exp.subst_apply F eX ≡α⟨S⟩ exp.subst_apply G eY :=
  λ P H, subst_preservation_core H F G @P

end

section

variables {eX₁ eX₂ : exp X}

-- Substitution preserves alpha equality.
def subst_preservation
(F : exp.subst X Y) (G : exp.subst X Y)
: subst_aeq F G (nrel.id X) (nrel.id Y)
→ eX₁ ≡α eX₂
→ exp.subst_apply F eX₁ ≡α exp.subst_apply G eX₂ :=
  subst_preservation_general F G

end

section

theorem self_aeq_subst_apply_lift (e : exp X)
: ∀ {Y : finset V} (F : X ν⇒ Y)
, e ≡α⟨nrel.lift F⟩ exp.subst_apply (exp.subst.lift F) e :=
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
      have H : e ≡α⟨nrel.lift (name.update a (finset.fresh Y).1 F)⟩ exp.subst_apply (exp.subst.lift (name.update a (finset.fresh Y).1 F)) e :=
        r (name.update a (finset.fresh Y).1 F),
      have P : exp.subst_update_var a (finset.fresh Y).1 (exp.subst.lift F) = exp.subst.lift (name.update a (finset.fresh Y).1 F) :=
        funext (exp.subst_update_var_eq_var_update a (finset.fresh Y).1 F),
      rw [←P] at H,
      exact (lam (map_simple nrel.update.lift H))
    end
  end

end

end aeq -- namespace -----------------------------------------------------------

end alpha
