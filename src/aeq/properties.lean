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
    rw [exp.insert_var.of_lam₂ e],
    have h : exp.subst.apply (exp.subst.update (fresh X).1 (fresh Y).1 F) (exp.lam (exp.map (vset.prop_subset_of_insert_comm (fresh X).1 a X) (exp.insert_var (fresh X).1 e)))
           = exp.lam (exp.subst.apply (exp.subst.update a (fresh (insert (fresh Y).1 Y)).1 (exp.subst.update (fresh X).1 (fresh Y).1 F)) (exp.map (vset.prop_subset_of_insert_comm (fresh X).1 a X) (exp.insert_var (fresh X).1 e))) :=
      exp.subst.apply.of_lam (exp.map (vset.prop_subset_of_insert_comm (fresh X).1 a X) (exp.insert_var (fresh X).1 e)),
    rw [h], clear h,
    rw [exp.subst.apply.of_lam e],
    rw [exp.insert_var.of_lam₂ (exp.subst.apply (exp.subst.update a (fresh Y).1 F) e)],
    apply aeq.lam,
    exact subst_comp.fresh_not_mem.within_lam F e @r
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
      simp [exp.subst.update],
      simp [exp.subst.apply],
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
theorem subst_comp.lam (F : exp.subst X Y) (G : exp.subst Y Z) (e : exp (insert a X))
(r : ∀ {Y Z : vs V} (F : exp.subst (insert a X) Y) (G : exp.subst Y Z)
   , exp.subst.apply G (exp.subst.apply F e)
       ≡α⟨vrel.id Z⟩
     exp.subst.apply (exp.subst.apply G ∘ F) e)
: exp.subst.apply (exp.subst.update (fresh Y).1 (fresh Z).1 G) (exp.subst.apply (exp.subst.update a (fresh Y).1 F) e)
    ≡α⟨vrel.id Z ⩁ ((fresh Z).1, (fresh Z).1)⟩
  exp.subst.apply (exp.subst.update a (fresh Z).1 (exp.subst.apply G ∘ F)) e :=
  aeq.map.simple (λ z₁ z₂, vrel.update.of_id ∘ vrel.is_identity.to_id (insert (fresh Z).1 Z)) $
    aeq.trans (r (exp.subst.update a (fresh Y).1 F) (exp.subst.update (fresh Y).1 (fresh Z).1 G))
              (subst_comp.preservation F G e)

-- Paper: Proposition 6.3 (e)
theorem subst_comp (F : exp.subst X Y) (G : exp.subst Y Z) (e : exp X)
: exp.subst.apply G (exp.subst.apply F e)
    ≡α⟨vrel.id Z⟩
  exp.subst.apply (exp.subst.apply G ∘ F) e :=
  begin
    induction e with
      /- var -/ X x
      /- app -/ X f e rf re
      /- lam -/ X a e r
      generalizing Y Z F G,
    begin /- var -/
      exact aeq.refl (exp.subst.apply G (F x))
    end,
    begin /- app -/
      exact aeq.app (rf F G) (re F G)
    end,
    begin /- lam -/
      exact aeq.lam (subst_comp.lam F G e @r)
    end
  end

end /- namespace -/ aeq --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
