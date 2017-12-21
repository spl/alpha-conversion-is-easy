/-

This file contains substitution preservation for `db` to `aeq`.

-/

import .injection
import .subst

namespace fin ------------------------------------------------------------------

variables {n : ℕ}

theorem succ_ne_zero : ∀ {N : fin n}, fin.succ N ≠ 0
  | ⟨m, m_lt_n⟩ := ne_of_vne (nat.succ_ne_zero m)

theorem pred_succ : ∀ {N : fin n} {p : fin.succ N ≠ 0}, pred (fin.succ N) p = N
  | ⟨m, m_lt_n⟩ p := rfl

theorem succ_eq_add_right_1 : ∀ {N : fin n}, fin.succ N = add_right 1 N
  | ⟨m, m_lt_n⟩ := rfl

end /- namespace -/ fin --------------------------------------------------------

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {e : exp X} -- Expressions
variables {m n : ℕ} -- De Bruijn indices
variables {ϕ ϕX : ν∈ X → fin m} {ϕY : ν∈ Y → fin n} -- De Bruijn injections
variables {F : exp.subst X Y} -- Expression substitutions
variables {G : db.subst m n} -- De Bruijn substitutions

theorem injection_pres_subst.lam₁
: (∀ (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ (∀ (x : ν∈ insert a X), inject (exp.subst.update a b F x) (inject.update b ϕY) = subst.update G (inject.update a ϕX x)) :=
  begin
    intros p x,
    cases x with x x_in_insert_a_X,
/-
    cases decidable.em (x = a),
    case or.inl : x_eq_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update, subst.update]},
      repeat { rw dif_pos x_eq_a },
      rw dif_pos (@eq.refl (fin (nat.succ m)) 0),
      simp [inject, vname.insert_self, inject.update]
    },
    case or.inr : x_ne_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update]},
      repeat { rw dif_neg x_ne_a },
    }
-/
    by_cases h : x = a,
    { /- h : x = a -/
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update, subst.update]},
      repeat {rw dif_pos h},
      rw dif_pos rfl,
      simp [inject, vname.insert_self, inject.update]
    },
    { /- h : x ≠ a -/
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update]},
      repeat {rw dif_neg h},
      simp [subst.update],
      rw dif_neg fin.succ_ne_zero,
      rw fin.pred_succ,
      generalize : vname.erase ⟨x, x_in_insert_a_X⟩ h = x',
      rw ← p x',
      generalize : F x' = e,
/-
      induction e,
      case exp.var : Y y {
/-
        simp [exp.insert_var, exp.map, inject, shift_var, shift, vname.map_of_subset, inject.update, vname.erase, fin.shift],
        rw if_neg (nat.not_lt_zero (ϕY y).val),
        cases y with y y_in_Y,
        by_cases h₂ : y = b,
        { /- h₂ : y = b -/
          rw dif_pos h₂,
        },
        { /- h₂ : y ≠ b -/
        }
-/
      },
-/
      admit
    }
  end

theorem injection_pres_subst.lam₂
: (∀ {X Y : vs V} {m n : ℕ} (F : exp.subst X Y) (G : db.subst m n) (ϕX : ν∈ X → fin m) (ϕY : ν∈ Y → fin n) (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ (∀ (x : ν∈ insert a X), inject (exp.subst.update a b F x) (inject.update b ϕY) = subst.update G (inject.update a ϕX x)) :=
  begin
    intros p x,
    cases x with x x_in_insert_a_X,
    cases decidable.em (x = a),
    case or.inl : x_eq_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update, subst.update]},
      repeat { rw dif_pos x_eq_a },
      rw dif_pos (@eq.refl (fin (nat.succ m)) 0),
      simp [inject, vname.insert_self, inject.update]
    },
    case or.inr : x_ne_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.update]},
      repeat { rw dif_neg x_ne_a },
      exact p (exp.insert_var b ∘ F) (subst.update G) (fin.succ ∘ ϕX) (inject.update b ϕY) (vname.erase ⟨x, x_in_insert_a_X⟩ x_ne_a)
    }
  end

theorem blah
: inject (exp.insert_var (fresh X).1 e) (inject.update (fresh X).1 ϕ) = shift_var (inject e ϕ) :=
  begin
    induction e,
    case exp.var : X x {
      rw exp.insert_var.of_var x,
      repeat {rw db.inject.var},
      simp [shift_var],
      -- rw db.shift.var 1 0 (ϕ x),
      simp only [shift],
      cases x with x x_in_X,
      simp [vname.insert, inject.update],
      cases fresh X with x' x'_not_in_X,
      rw dif_neg (vname.ne_if_mem_and_not_mem ⟨x, x_in_X⟩ ⟨x', x'_not_in_X⟩),
      simp [fin.shift],
      rw if_neg (nat.not_lt_zero (ϕ ⟨x, x_in_X⟩).val),
      simp [vname.erase],
      rw ← fin.succ_eq_add_right_1,
      refl
    },
    case exp.app : X f e rf re {
      simp [shift_var],
      rw inject.app,
      -- rw shift.app m 1 0 (inject f ϕ) (inject e ϕ),
      simp [shift],
      rw exp.insert_var.of_app f e,
      rw inject.app,
      rw [rf, re],
      refl
    },
    case exp.lam : X a e r {
      rw inject.lam,
      simp only [shift_var, shift],
      rw exp.insert_var.of_lam₃ e,
      rw inject.lam,
    }
  end

theorem injection_pres_subst.lam₃
: (∀ (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ ∀ (x : ν∈ insert a X), inject (exp.subst.update a (fresh Y).1 F x) (inject.update (fresh Y).1 ϕY) = subst.update G (inject.update a ϕX x) :=
  begin
    intros p x,
    cases x with x x_in_insert_a_X,
    -- cases fresh Y with y y_not_in_Y,
    simp [exp.subst.update, db.inject.update],
    by_cases h : x = a,
    { /- h : x = a -/
      repeat {rw dif_pos h},
      rw inject.var,
      simp [db.subst.update, db.inject.update]
    },
    { /- h₂ : x ≠ a -/
      repeat {rw dif_neg h},
      simp [db.subst.update],
      rw dif_neg fin.succ_ne_zero,
      rw fin.pred_succ,
      generalize : vname.erase ⟨x, x_in_insert_a_X⟩ h = x',
      rw ← p x',
      generalize : F x' = e,
     exact blah
    }
  end

theorem injection_pres_subst₁
: (∀ (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ inject (exp.subst.apply F e) ϕY = db.subst.apply G (inject e ϕX) :=
  begin
    induction e generalizing Y m n ϕX ϕY F G,
    case exp.var : X x {
      intro p,
      exact p x
    },
    case exp.app : X fX eX rf re {
      intro p,
      conv {to_lhs, simp [exp.subst.apply, inject]},
      conv {to_rhs, simp [inject, db.subst.apply]},
      rw [rf p, re p],
      refl
    },
    case exp.lam : X a eX r {
      intro p,
      rw exp.subst.apply.of_lam eX,
      rw db.inject.lam (exp.subst.apply _ _),
      rw db.inject.lam eX,
      rw db.subst.apply.lam (inject _ _),
      rw r (injection_pres_subst.lam₃ p)
    }
  end

theorem injection_pres_subst₂
(p : ∀ {X Y : vs V} {m n : ℕ} (F : exp.subst X Y) (G : db.subst m n) (ϕX : ν∈ X → fin m) (ϕY : ν∈ Y → fin n) (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
: inject (exp.subst.apply F e) ϕY = db.subst.apply G (inject e ϕX) :=
  begin
    induction e generalizing Y m n ϕX ϕY F G,
    case exp.var : X x {
      exact p F G ϕX ϕY x
    },
    case exp.app : X fX eX rf re {
      conv {to_lhs, simp [exp.subst.apply, inject]},
      conv {to_rhs, simp [inject, db.subst.apply]},
      rw [rf, re],
      refl
    },
    case exp.lam : X a eX r {
      conv {to_lhs, simp [exp.subst.apply, inject]},
      conv {to_rhs, simp [inject, db.subst.apply]},
      rw r,
      refl
    }
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
