/-

This file contains substitution preservation for `db` to `aeq`.

-/

import .injection
import .subst

theorem fin.succ_ne_zero {n : ℕ} : ∀ {N : fin n}, fin.succ N ≠ 0
  | ⟨m, m_lt_n⟩ := fin.ne_of_vne (nat.succ_ne_zero m)

theorem fin.pred_succ {n : ℕ} : ∀ {N : fin n} {p : fin.succ N ≠ 0}, fin.pred (fin.succ N) p = N
  | ⟨m, m_lt_n⟩ p := rfl

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {e : exp X} -- Expressions
variables {m n : ℕ} -- De Bruijn indices
variables {ϕX : ν∈ X → fin m} {ϕY : ν∈ Y → fin n} -- De Bruijn injections
variables {F : exp.subst X Y} -- Expression substitutions
variables {G : db.subst m n} -- De Bruijn substitutions

theorem injection_pres_subst.lam₁
: (∀ (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ (∀ (x : ν∈ insert a X), inject (exp.subst.update a b F x) (inject.lam b ϕY) = subst.update G (inject.lam a ϕX x)) :=
  begin
    intros p x,
    cases x with x x_in_insert_a_X,
/-
    cases decidable.em (x = a),
    case or.inl : x_eq_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam, subst.update]},
      repeat { rw dif_pos x_eq_a },
      rw dif_pos (@eq.refl (fin (nat.succ m)) 0),
      simp [inject, vname.insert_self, inject.lam]
    },
    case or.inr : x_ne_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam]},
      repeat { rw dif_neg x_ne_a },
    }
-/
    by_cases h : x = a,
    { /- h : x = a -/
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam, subst.update]},
      repeat {rw dif_pos h},
      rw dif_pos rfl,
      simp [inject, vname.insert_self, inject.lam]
    },
    { /- h : x ≠ a -/
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam]},
      repeat {rw dif_neg h},
      simp [subst.update],
      rw dif_neg fin.succ_ne_zero,
      rw fin.pred_succ,
      admit
    }
  end

theorem injection_pres_subst.lam₂
: (∀ {X Y : vs V} {m n : ℕ} (F : exp.subst X Y) (G : db.subst m n) (ϕX : ν∈ X → fin m) (ϕY : ν∈ Y → fin n) (x : ν∈ X), inject (F x) ϕY = G (ϕX x))
→ (∀ (x : ν∈ insert a X), inject (exp.subst.update a b F x) (inject.lam b ϕY) = subst.update G (inject.lam a ϕX x)) :=
  begin
    intros p x,
    cases x with x x_in_insert_a_X,
    cases decidable.em (x = a),
    case or.inl : x_eq_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam, subst.update]},
      repeat { rw dif_pos x_eq_a },
      rw dif_pos (@eq.refl (fin (nat.succ m)) 0),
      simp [inject, vname.insert_self, inject.lam]
    },
    case or.inr : x_ne_a {
      simp [exp.subst.update],
      conv {to_rhs, simp [inject.lam]},
      repeat { rw dif_neg x_ne_a },
      exact p (exp.insert_var b ∘ F) (subst.update G) (fin.succ ∘ ϕX) (inject.lam b ϕY) (vname.erase ⟨x, x_in_insert_a_X⟩ x_ne_a)
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
      conv {to_lhs, simp [exp.subst.apply, inject]},
      conv {to_rhs, simp [inject, db.subst.apply]},
      rw r (injection_pres_subst.lam₁ p),
      refl
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
