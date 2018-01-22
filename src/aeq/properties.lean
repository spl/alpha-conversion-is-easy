/-

This file contains properties of `aeq`.

-/

import .subst

namespace acie ------------------------------------------------------------------
namespace aeq ------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y Z : vs V} -- Variable name sets
variables {R : X ×ν Y} {S : Y ×ν Z} -- Variable name set relations
variables {eX : exp X} {eY eY₁ eY₂ : exp Y} {eZ : exp Z} -- Expressions

-- Paper: Lemma 7
theorem self_lift_F_aeq_subst_lift_F (F : X →ν Y) (e : exp X)
: e ≡α⟨vrel.lift F⟩ exp.subst.apply (exp.subst.lift F) e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r
      generalizing Y F,
    begin /- var -/
      exact var rfl
    end,
    begin /- app -/
      exact app (rf F) (re F)
    end,
    begin /- lam -/
      have H : e ≡α⟨vrel.lift (vname.update a (fresh Y).1 F)⟩ exp.subst.apply (exp.subst.lift (vname.update a (fresh Y).1 F)) e :=
        r (vname.update a (fresh Y).1 F),
      have P : exp.subst.update a (fresh Y).1 (exp.subst.lift F) = exp.subst.lift (vname.update a (fresh Y).1 F) :=
        funext (exp.subst.update_eq_var_update a (fresh Y).1 F),
      rw [←P] at H,
      exact (lam (map.simple vrel.update.lift H))
    end
  end

-- Paper: Proposition 6.1 (a)
theorem self_aeq_subst_var (e : exp X)
: e ≡α⟨vrel.id X⟩ exp.subst.apply (exp.subst.id X) e :=
  map.simple (λ x y p, psigma.eq p rfl) (self_lift_F_aeq_subst_lift_F id e)

constant subst_comp.fresh_not_mem.within_lam
(F : exp.subst X Y) (e : exp (insert a X))
(r : ∀ {Y : vs V} (F : exp.subst (insert a X) Y),
  exp.subst.apply (exp.subst.update ((fresh (insert a X)).1) (fresh Y).1 F) (exp.insert_var ((fresh (insert a X)).1) e)
    ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩
  exp.insert_var (fresh Y).1 (exp.subst.apply F e))
: exp.subst.apply
      (exp.subst.update a (fresh (insert (fresh Y).1 Y)).1 (exp.subst.update (fresh X).1 (fresh Y).1 F))
      (exp.map (vset.prop_subset_of_insert_comm (fresh X).1 a X) (exp.insert_var (fresh X).1 e))
    ≡α⟨vrel.id (insert (fresh Y).1 Y) ⩁ ((fresh (insert (fresh Y).1 Y)).1, (fresh Y).1)⟩
  exp.map
      (vset.prop_subset_of_insert_comm (fresh Y).1 (fresh Y).1 Y)
      (exp.insert_var (fresh Y).1 (exp.subst.apply (exp.subst.update a (fresh Y).1 F) e))

theorem subst_comp.fresh_not_mem.lam (F : exp.subst X Y) (e : exp (insert a X))
(r : ∀ {Y : vs V} (F : exp.subst (insert a X) Y),
  exp.subst.apply (exp.subst.update ((fresh (insert a X)).1) (fresh Y).1 F) (exp.insert_var ((fresh (insert a X)).1) e)
    ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩
  exp.insert_var (fresh Y).1 (exp.subst.apply F e))
: exp.subst.apply (exp.subst.update (fresh X).1 (fresh Y).1 F) (exp.insert_var (fresh X).1 (exp.lam e))
    ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩
  exp.insert_var (fresh Y).1 (exp.subst.apply F (exp.lam e)) :=
  begin
    rw [exp.insert_var.lam_comp e],
    rw [exp.subst.apply, exp.subst.apply],
    rw [exp.insert_var.lam_comp (exp.subst.apply (exp.subst.update a (fresh Y).1 F) e)],
    exact aeq.lam (subst_comp.fresh_not_mem.within_lam F e @r)
  end

-- Paper: Proposition 6.3 (a)
theorem subst_comp.fresh_not_mem (F : exp.subst X Y) (e : exp X)
: exp.subst.apply (exp.subst.update (fresh X).1 (fresh Y).1 F) (exp.insert_var (fresh X).1 e)
    ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩
  exp.insert_var (fresh Y).1 (exp.subst.apply F e) :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r
      generalizing Y F,
    begin /- var -/
      rw [exp.insert_var],
      simp [exp.map, exp.subst.apply, exp.subst.update],
      rw [dif_neg (vname.ne_if_mem_and_not_mem (vname.map_of_subset (vset.prop_subset_refl X) x) (fresh X))],
      cases x with x px,
      exact aeq.refl (exp.insert_var (fresh Y).1 (F ⟨x, px⟩)),
    end,
    begin /- app -/
      exact aeq.app (rf F) (re F)
    end,
    begin /- lam -/
      exact subst_comp.fresh_not_mem.lam F e @r
    end
  end

-- Paper: Proposition 6.3 (b)
theorem subst_comp.extend (a : V) (F : exp.subst X Y) (G : exp.subst Y Z)
: aeq.extend
    (exp.subst.apply (exp.subst.update (fresh Y).1 (fresh Z).1 G) ∘ exp.subst.update a (fresh Y).1 F)
    (exp.subst.update a (fresh Z).1 (exp.subst.apply G ∘ F))
    (vrel.id (insert a X))
    (vrel.id (insert (fresh Z).1 Z)) :=
  begin
    intros x y h,
    induction h,
    simp [function.comp],
    cases x with x px,
    cases decidable.em (x = a) with x_eq_a x_ne_a,
    begin /- x_eq_a : x = a -/
      induction x_eq_a,
      simp [exp.subst.update, exp.subst.apply],
      exact aeq.refl (exp.var (vname.insert_self (fresh Z).1 Z))
    end,
    begin /- x_ne_a : x ≠ a -/
      rw [exp.subst.update_of_ne a (fresh Y).1 F ⟨x, px⟩ x_ne_a],
      rw [exp.subst.update_of_ne a (fresh Z).1 (exp.subst.apply G ∘ F) ⟨x, px⟩ x_ne_a],
      simp [function.comp],
      exact subst_comp.fresh_not_mem G (F (vname.erase ⟨x, px⟩ x_ne_a))
    end
  end

-- Paper: Proposition 6.3 (c)
theorem subst_comp.preservation (F : exp.subst X Y) (G : exp.subst Y Z) (e : exp (insert a X))
: exp.subst.apply (exp.subst.apply (exp.subst.update (fresh Y).1 (fresh Z).1 G) ∘ exp.subst.update a (fresh Y).1 F) e
    ≡α⟨vrel.id Z ⩁ ((fresh Z).1, (fresh Z).1)⟩
  exp.subst.apply (exp.subst.update a (fresh Z).1 (exp.subst.apply G ∘ F)) e :=
  aeq.map.simple (λ z₁ z₂, vrel.is_identity.from_id (vrel.id Z ⩁ ((fresh Z).1, (fresh Z).1))) $
    aeq.subst_preservation.id (exp.subst.apply (exp.subst.update (fresh Y).1 (fresh Z).1 G) ∘ exp.subst.update a (fresh Y).1 F)
                              (exp.subst.update a (fresh Z).1 (exp.subst.apply G ∘ F))
                              (subst_comp.extend a F G)
                              (aeq.refl e)

-- Paper: Proposition 6.3 (d)
theorem subst_comp
: ∀ {X Y Z : vs V} (F : exp.subst X Y) (G : exp.subst Y Z) (e : exp X)
, exp.subst.apply G (exp.subst.apply F e)
    ≡α⟨vrel.id Z⟩
  exp.subst.apply (exp.subst.apply G ∘ F) e
  | X Y Z F G (exp.var x)              := aeq.refl (exp.subst.apply G (F x))
  | X Y Z F G (exp.app f e)            := aeq.app (subst_comp F G f) (subst_comp F G e)
  | X Y Z F G (@exp.lam _ _ _ _ _ a e) := aeq.lam $
    let b := (fresh Y).1 in
    let c := (fresh Z).1 in
    have update_id_from_comp_id
        : ∀ (z₁ : ν∈ insert c Z) (z₂ : ν∈ insert c Z)
        , (vrel.id (insert c Z) ⨾ vrel.id Z ⩁ (c, c)) z₁ z₂
        → vrel.id Z ⩁ (c, c) z₁ z₂ :=
      λ z₁ z₂, vrel.update.of_id ∘ vrel.is_identity.to_id (insert c Z),
    aeq.map.simple update_id_from_comp_id $
      aeq.trans (subst_comp (exp.subst.update a b F) (exp.subst.update b c G) e)
                (aeq.subst_comp.preservation F G e)

----------------------------------------------------------------------------------------------------

set_option pp.proofs true

/-
theorem blah₁ : ∀ {X : vs V} (e : exp (insert (fresh X).1 X))
, exp.insert_var (fresh (insert (fresh X).1 X)).1 e
    ≡α⟨vrel.id (insert (fresh X).1 X) ⩁ ((fresh (insert (fresh X).1 X)).1, (fresh X).1)⟩
  exp.insert_var (fresh X).1 e
  | X (exp.var x)              :=
    begin
      rw [exp.insert_var.var, exp.insert_var.var],
      apply aeq.var,
      unfold vrel.update,
      unfold vrel.id,
      right,
      have px : (vname.insert (fresh (insert (fresh X).1 X)).1 x).1 ≠ (fresh (insert (fresh X).1 X)).1,
        begin
          unfold vname.insert,
          exact vname.ne_if_mem_and_not_mem x (fresh (insert (fresh X).1 X))
        end,
      existsi px,
      have py : (vname.insert (fresh X).1 x).1 ≠ (fresh X).1,
        begin
          unfold vname.insert,
          unfold vname.insert at px,
        end,
      existsi py,
    end
  | X (exp.app f e)            := sorry
  | X (@exp.lam _ _ _ _ _ a e) := sorry
-/

theorem subst_comp₂.fresh_not_mem : ∀ {X Y : vs V} (F : exp.subst X Y) (e : exp X)
, exp.subst.apply (exp.subst.update (fresh X).1 (fresh Y).1 F) (exp.insert_var (fresh X).1 e)
    ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩
  exp.insert_var (fresh Y).1 (exp.subst.apply F e)
  | X Y F (exp.var x) :=
    begin
      rw [exp.insert_var.var, exp.subst.apply, exp.subst.apply],
      have h : (vname.insert (fresh X).1 x).1 ≠ (fresh X).1 :=
        vname.ne_if_mem_and_not_mem (vname.map_of_subset (vset.prop_subset_refl X) x) (fresh X),
      rw [exp.subst.update.ne (fresh Y).1 F h, vname.eq_of_erase_insert x h],
      exact aeq.refl (exp.insert_var (fresh Y).1 (F x))
    end
  | X Y F (exp.app f e) :=
    aeq.app (subst_comp₂.fresh_not_mem F f) (subst_comp₂.fresh_not_mem F e)
  | X Y F (@exp.lam _ _ _ _ _ a e) :=
    begin
/-
      rw [exp.insert_var.lam_comp, exp.subst.apply, exp.subst.apply, exp.insert_var.lam_comp],
      apply aeq.lam,
      rw vset.prop_subset_of_insert_comm_refl (fresh Y).1 Y,
      rw ←exp.map.id (exp.insert_var (fresh Y).1 (exp.subst.apply (exp.subst.update a (fresh Y).1 F) e)),
-/
/-
      have h : (fresh X).1 = a := sorry,
      induction h,
      rw vset.prop_subset_of_insert_comm_refl (fresh X).1 X,
      rw ←exp.map.id (exp.insert_var (fresh X).1 e),
-/
      let a' := (fresh X).1,
      let b' := (fresh Y).1,
      let b'' := (fresh (insert b' Y)).1,
      have r :
        exp.subst.apply (exp.subst.update (fresh (insert a X)).1 b'' (exp.subst.update a b' F)) (exp.insert_var (fresh (insert a X)).1 e)
          ≡α⟨vrel.id (insert b'' (insert b' Y))⟩
        exp.insert_var b'' (exp.subst.apply (exp.subst.update a b' F) e) :=
          subst_comp₂.fresh_not_mem (exp.subst.update a b' F) e,
      rw exp.subst.apply,
      rw exp.insert_var.lam_comp (exp.subst.apply (exp.subst.update a b' F) e),
      rw exp.insert_var.lam_comp e,
      rw exp.subst.apply,
      apply aeq.lam,
      have h : (fresh X).1 = a' := rfl, rw h, clear h,
      have h : (fresh Y).1 = b' := rfl, rw h, clear h,
      have h : (fresh (insert b' Y)).1 = b'' := rfl, rw h, clear h,
      rw vset.prop_subset_of_insert_comm_refl b' Y,
      rw ←exp.map.id (exp.insert_var b' (exp.subst.apply (exp.subst.update a b' F) e)),
      have upd₂ : ∀ (y₁ : ν∈ insert b'' (insert b' Y)) (y₂ : ν∈ insert b' (insert b' Y))
        , ⟪y₁, y₂⟫ ∈ν vrel.id (insert b' Y) ⩁ (b'', b'') ⨾ vrel.id (insert b' Y) ⩁ (b'', b')
        → ⟪y₁, y₂⟫ ∈ν vrel.id (insert b' Y) ⩁ (b'', b') :=
          λ y₁ y₂, vrel.update.id.of_comp ∘ vrel.update.of_comp,
      apply aeq.map.simple upd₂,
      show
        exp.subst.apply (exp.subst.update a b'' (exp.subst.update a' b' F)) (exp.map (vset.prop_subset_of_insert_comm a' a X) (exp.insert_var a' e))
          ≡α⟨vrel.id (insert b' Y) ⩁ (b'', b'') ⨾ vrel.id (insert b' Y) ⩁ (b'', b')⟩
        exp.insert_var b' (exp.subst.apply (exp.subst.update a b' F) e), from sorry
    end

lemma subst_comp₂.extend (a : V) (F : exp.subst X Y) (G : exp.subst Y Z)
: aeq.extend
    (exp.subst.apply (exp.subst.update (fresh Y).1 (fresh Z).1 G) ∘ exp.subst.update a (fresh Y).1 F)
    (exp.subst.update a (fresh Z).1 (exp.subst.apply G ∘ F))
    (vrel.id (insert a X))
    (vrel.id (insert (fresh Z).1 Z)) :=
  λ (x₁ : ν∈ insert a X) (x₂ : ν∈ insert a X) (p : ⟪x₁, x₂⟫ ∈ν vrel.id (insert a X)),
  begin
    let b' := (fresh Y).1, let c' := (fresh Z).1,
    have p : x₁ = x₂, from p,
    induction p, clear p,
    rw function.comp, simp,
    by_cases h : x₁.1 = a,
    { /- h : x₁.1 = a -/
      rw exp.subst.update.eq b' F h,
      rw exp.subst.update.eq c' (exp.subst.apply G ∘ F) h,
      rw exp.subst.apply,
      simp [vname.insert_self],
      have h : (psigma.mk b' _).1 = b' := rfl,
      rw exp.subst.update.eq c' G h,
      simp [vname.insert_self],
      exact aeq.refl (exp.var ⟨c', _⟩)
    },
    { /- h : x₁.1 ≠ a -/
      calc
        exp.subst.apply (exp.subst.update b' c' G) (exp.subst.update a b' F x₁)
            =
        exp.subst.apply (exp.subst.update b' c' G) (exp.insert_var b' (F (vname.erase x₁ h)))
            : by rw exp.subst.update.ne b' F h
        ... ≡α⟨vrel.id (insert c' Z)⟩
        exp.insert_var c' (exp.subst.apply G (F (vname.erase x₁ h)))
            : subst_comp₂.fresh_not_mem G (F (vname.erase x₁ h))
        ... =
        exp.subst.update a c' (exp.subst.apply G ∘ F) x₁
            : by rw ←exp.subst.update.ne c' (exp.subst.apply G ∘ F) h
    }
  end

theorem subst_comp₂
: ∀ {X Y Z : vs V} (F : exp.subst X Y) (G : exp.subst Y Z) (e : exp X)
, exp.subst.apply G (exp.subst.apply F e)
    ≡α⟨vrel.id Z⟩
  exp.subst.apply (exp.subst.apply G ∘ F) e
  | X Y Z F G (exp.var x)              := aeq.refl (exp.subst.apply G (F x))
  | X Y Z F G (exp.app f e)            := aeq.app (subst_comp F G f) (subst_comp F G e)
  | X Y Z F G (@exp.lam _ _ _ _ _ a e) := aeq.lam $
    let b' := (fresh Y).1, c' := (fresh Z).1 in
    aeq.map.simple (λ z₁ z₂, vrel.update.of_id) $
    calc
      exp.subst.apply (exp.subst.update b' c' G) (exp.subst.apply (exp.subst.update a b' F) e)
          ≡α⟨vrel.id (insert c' Z)⟩
      exp.subst.apply (exp.subst.apply (exp.subst.update b' c' G) ∘ exp.subst.update a b' F) e
          : subst_comp₂ (exp.subst.update a b' F) (exp.subst.update b' c' G) e
      ... ≡α⟨vrel.id (insert c' Z)⟩
      exp.subst.apply (exp.subst.update a c' (exp.subst.apply G ∘ F)) e
          : subst_preservation.id _ _ (aeq.subst_comp₂.extend a F G) (aeq.refl e)

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
