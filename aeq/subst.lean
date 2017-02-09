/-

This file contains the proof that substitution preserves alpha equality.

-/

import .map

open [notation] eq.ops
open [class] [notation] finset
open [notation] function
open [notation] sigma.ops
open [notation] vrel

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `finset V` is the type of a finite set of variable names with freshness.
variables [finset.has_fresh V]

namespace aeq -- ===============================================================

variables {X₁ Y₁ X₂ Y₂ : finset V}

-- This is the type of a function that lifts a relation `R` to an alpha-equality
-- relation on `S` with the substitutions `F` and `G` applied to each side.
definition subst_aeq
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
(R : vrel X₁ Y₁) (S : vrel X₂ Y₂) :=

  ∀ {x : ν∈ X₁} {y : ν∈ Y₁}, ⟪x, y, R⟫ → aeq S (F x) (G y)

variables {F : exp.subst X₁ X₂} {G : exp.subst Y₁ Y₂}
variables {R : vrel X₁ Y₁} {S : vrel X₂ Y₂}
variables {a b : V}

-- A lemma needed for the `lam` case in `subst_preservation_core`.
lemma subst_preservation_update (nx₂ : ν∉ X₂) (ny₂ : ν∉ Y₂)
: subst_aeq F G R S
→ subst_aeq
    (exp.subst_update_var a nx₂.1 F)
    (exp.subst_update_var b ny₂.1 G)
    (vrel.update a b R)
    (vrel.update nx₂.1 ny₂.1 S) :=

  begin
    intro P x₁ y₁ H,
    cases H with H H,
    begin
      cases H,
      rewrite [dif_pos `x₁.1 = a`, dif_pos `y₁.1 = b`],
      apply var, left, split, reflexivity, reflexivity
    end,
    begin
      cases H with x_ne_a₁ H,
      cases H with y_ne_b₁ x₁_R_y₁,
      rewrite [dif_neg `x₁.1 ≠ a`, dif_neg `y₁.1 ≠ b`],
      apply map (finset.subset_insert X₂ nx₂.1) (finset.subset_insert Y₂ ny₂.1),
      rotate_left 1,
      begin
        exact P x₁_R_y₁,
      end,
      begin
        intro x₂ y₂ c_S_d,
        cases x₂ with x₂ px₂, cases y₂ with y₂ py₂,
        existsi cvar.insert_constraint nx₂.1 px₂,
        existsi cvar.insert_constraint ny₂.1 py₂,
        right,
        existsi finset.ne_of_mem_of_not_mem px₂ nx₂.2,
        existsi finset.ne_of_mem_of_not_mem py₂ ny₂.2,
        exact c_S_d
      end
    end
  end

variables {eX : exp X₁} {eY : exp Y₁}

-- The implementation of `subst_preservation`.
lemma subst_preservation_core (H : aeq R eX eY)
: ∀ {X₂ Y₂ : finset V} {S : vrel X₂ Y₂}
    (F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
    (P : subst_aeq F G R S)
, aeq S (exp.subst_apply F eX) (exp.subst_apply G eY) :=

  begin
    induction H with
      /- var -/ X₁ Y₁ R x y x_R_y
      /- app -/ X₁ Y₁ R fX eX fY eY af ae rf re
      /- lam -/ X₁ Y₁ R x y eX eY a r,
    begin /- var -/
      intro X₂ Y₂ S F G P,
      exact P x_R_y
    end,
    begin /- app -/
      intro X₂ Y₂ S F G P,
      exact app (rf F G @P) (re F G @P)
    end,
    begin /- lam -/
      intro X₂ Y₂ S F G P,
      apply lam,
      exact r
        (exp.subst_update_var x (finset.fresh X₂).1 F)
        (exp.subst_update_var y (finset.fresh Y₂).1 G)
        (λ x y, subst_preservation_update (finset.fresh X₂) (finset.fresh Y₂) @P)
    end
  end

-- General form of substitution preserves alpha equality property.
theorem subst_preservation_general
(F : exp.subst X₁ X₂) (G : exp.subst Y₁ Y₂)
: subst_aeq F G R S
→ aeq R eX eY
→ aeq S (exp.subst_apply F eX) (exp.subst_apply G eY) :=

  λ P H, subst_preservation_core H F G @P

end aeq -- namespace -----------------------------------------------------------

namespace aeq -- ===============================================================

variables {X Y : finset V}
variables {eX₁ eX₂ : exp X}

-- Substitution preserves alpha equality.
theorem subst_preservation
(F : exp.subst X Y) (G : exp.subst X Y)
: subst_aeq F G (vrel.id X) (vrel.id Y)
→ aeq (vrel.id X) eX₁ eX₂
→ aeq (vrel.id Y) (exp.subst_apply F eX₁) (exp.subst_apply G eX₂) :=

  subst_preservation_general F G

end aeq -- namespace -----------------------------------------------------------
