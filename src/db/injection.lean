/-

This file contains the injection of `db` into `exp`.

-/

import .type
import aeq
import data.fin

namespace fin ------------------------------------------------------------------

variables {n : ℕ} {a b : fin n}

protected
theorem succ.inj (p : fin.succ a = fin.succ b) : a = b :=
  by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

end /- namespace -/ fin --------------------------------------------------------

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {R : X ×ν Y} -- Variable name set relations
variables {n : ℕ} -- De Bruijn indices
variables {ϕX ϕ : ν∈ X → fin n} {ϕY : ν∈ Y → fin n} -- Injections
variables {eX e₁ e₂ : exp X} {eY : exp Y} -- Expressions

def inject.lam (a : V) (ϕ : ν∈ X → fin n) (x : ν∈ (insert a X)) : fin (nat.succ n) :=
  if p : x.1 = a then fin.of_nat 0 else fin.succ $ ϕ $ vname.erase x p

def inject : ∀ {X : vs V}, exp X → ∀ {n : ℕ}, (ν∈ X → fin n) → db n
  | X (exp.var x)              n ϕ := db.var $ ϕ x
  | X (exp.app f e)            n ϕ := db.app (inject f ϕ) (inject e ϕ)
  | X (@exp.lam _ _ _ _ _ a e) n ϕ := db.lam $ inject e $ acie.db.inject.lam a ϕ

theorem Rdef.lam.mp (Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕX x = ϕY y))
(x : ν∈ insert a X) (y : ν∈ insert b Y) (R' : R ⩁ (a, b) x y)
: inject.lam a ϕX x = inject.lam b ϕY y :=
  begin
    simp [inject.lam],
    cases decidable.em (x.1 = a),
    case or.inl x_eq_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        rw [dif_pos x_eq_a, dif_pos y_eq_b]
      },
      case or.inr y_ne_b {
        cases R',
        case or.inl p { cases p with _ y_eq_b, contradiction },
        case or.inr p { cases p with x_ne_a, contradiction }
      }
    },
    case or.inr x_ne_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        cases R',
        case or.inl p { cases p with x_eq_a, contradiction },
        case or.inr p { cases p with _ p, cases p with y_ne_b, contradiction }
      },
      case or.inr y_ne_b {
        cases R',
        case or.inl p { cases p with x_eq_a, contradiction },
        case or.inr p {
          cases p with px p, cases p with py p,
          rw [dif_neg x_ne_a, dif_neg y_ne_b],
          have h : ϕX (vname.erase x px) = ϕY (vname.erase y py), from
            iff.mp (Rdef (vname.erase x px) (vname.erase y py)) p,
          simp [vname.erase] at *,
          rw h
        }
      }
    }
  end

theorem Rdef.lam.mpr (Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕX x = ϕY y))
(x : ν∈ insert a X) (y : ν∈ insert b Y) (P : inject.lam a ϕX x = inject.lam b ϕY y)
: R ⩁ (a, b) x y :=
  begin
    simp [vrel.update],
    simp [inject.lam] at P,
    cases decidable.em (x.1 = a),
    case or.inl x_eq_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        exact or.inl ⟨x_eq_a, y_eq_b⟩
      },
      case or.inr y_ne_b {
        rw [dif_pos x_eq_a, dif_neg y_ne_b] at P,
        cases ϕY (vname.erase y y_ne_b) with m,
        have h : 0 = nat.succ m, from fin.veq_of_eq P,
        cases h
      }
    },
    case or.inr x_ne_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        rw [dif_neg x_ne_a, dif_pos y_eq_b] at P,
        cases ϕX (vname.erase x x_ne_a) with m,
        have h : nat.succ m = 0, from fin.veq_of_eq P,
        cases h
      },
      case or.inr y_ne_b {
        rw [dif_neg x_ne_a, dif_neg y_ne_b] at P,
        right,
        existsi x_ne_a, existsi y_ne_b,
        have P : ϕX (vname.erase x x_ne_a) = ϕY (vname.erase y y_ne_b), from
          fin.succ.inj P,
        exact iff.mpr (Rdef (vname.erase x x_ne_a) (vname.erase y y_ne_b)) P
      }
    }
  end

theorem Rdef.lam (Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕX x = ϕY y))
(x : ν∈ insert a X) (y : ν∈ insert b Y)
: R ⩁ (a, b) x y ↔ inject.lam a ϕX x = inject.lam b ϕY y :=
  ⟨acie.db.Rdef.lam.mp Rdef x y, acie.db.Rdef.lam.mpr Rdef x y⟩

theorem aeq_iff_inject (Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕX x = ϕY y))
: (eX ≡α⟨R⟩ eY) ↔ (inject eX ϕX = inject eY ϕY) :=
  begin
    induction eX generalizing Y n ϕX ϕY R Rdef eY,
    case exp.var X x {
      cases eY,
      case exp.var y {
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have h : ϕX x = ϕY y, from iff.mp (Rdef x y) (aeq.var.prop α),
          rw h
        end,
        begin /- iff.mpr -/
          intro p,
          have h : R x y, from iff.mpr (Rdef x y) (db.var.inj p),
          exact aeq.var h
        end
      },
      repeat { split, repeat { intro x, cases x } }
    },
    case exp.app X fX eX rf re {
      cases eY,
      case exp.app fY eY {
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have αf : fX ≡α⟨R⟩ fY, from aeq.app.fun α,
          have αe : eX ≡α⟨R⟩ eY, from aeq.app.arg α,
          have pf : inject fX ϕX = inject fY ϕY, from iff.mp (rf Rdef) αf,
          have pe : inject eX ϕX = inject eY ϕY, from iff.mp (re Rdef) αe,
          rw [pf, pe]
        end,
        begin /- iff.mpr -/
          intro p,
          have h : inject fX ϕX = inject fY ϕY ∧ inject eX ϕX = inject eY ϕY, from
            db.app.inj p,
          have αf : fX ≡α⟨R⟩ fY, from iff.mpr (rf Rdef) h.1,
          have αe : eX ≡α⟨R⟩ eY, from iff.mpr (re Rdef) h.2,
          exact aeq.app αf αe
        end
      },
      repeat { split, repeat { intro x, cases x } }
    },
    case exp.lam X a eX r {
      cases eY,
      case exp.lam b eY {
        have Rdef' : ∀ x y, R ⩁ (a, b) x y ↔ inject.lam a ϕX x = inject.lam b ϕY y, from
          acie.db.Rdef.lam Rdef,
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have α : eX ≡α⟨R ⩁ (a, b)⟩ eY, from aeq.lam.body α,
          have p : inject eX (inject.lam a ϕX) = inject eY (inject.lam b ϕY), from
            iff.mp (r Rdef') α,
          rw p
        end,
        begin /- iff.mpr -/
          intro p,
          have h : inject eX (inject.lam a ϕX) = inject eY (inject.lam b ϕY), from
            db.lam.inj p,
          have α : eX ≡α⟨R ⩁ (a, b)⟩ eY, from iff.mpr (r Rdef') h,
          exact aeq.lam α
        end
      },
      repeat { split, repeat { intro x, cases x } }
    }
  end

theorem aeq_iff_inject.id (inj : function.injective ϕ)
 : (e₁ ≡α e₂) ↔ (inject e₁ ϕ = inject e₂ ϕ) :=
  aeq_iff_inject $ λ x₁ x₂,
    ⟨ λ (p : vrel.id X x₁ x₂), by simp [vrel.id] at p; rw p
    , λ (p : ϕ x₁ = ϕ x₂), inj p
    ⟩

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
