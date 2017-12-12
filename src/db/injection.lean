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
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {n : ℕ} -- De Bruijn indexes

def inject.lam (a : V) (ϕ : ν∈ X → fin n) (x : ν∈ (insert a X)) : fin (nat.succ n) :=
  if p : x.1 = a then fin.of_nat 0 else fin.succ $ ϕ $ vname.erase x p

def inject : ∀ {X : vs V}, exp X → ∀ {n : ℕ}, (ν∈ X → fin n) → db n
  | X (exp.var x)              n ϕ := db.var $ ϕ x
  | X (exp.app f e)            n ϕ := db.app (inject f ϕ) (inject e ϕ)
  | X (@exp.lam _ _ _ _ _ a e) n ϕ := db.lam $ inject e $ acie.db.inject.lam a ϕ

def blah (ϕ₁ : ν∈ X → fin n) (ϕ₂ : ν∈ Y → fin n) : X ×ν Y:=
  λ (x : ν∈ X) (y : ν∈ Y), ϕ₁ x = ϕ₂ y

def blah.lam (ϕ₁ : ν∈ X → fin n) (ϕ₂ : ν∈ Y → fin n) : X ×ν Y:=
  λ (x : ν∈ X) (y : ν∈ Y), ϕ₁ x = ϕ₂ y

def inj_Rdef_mp {ϕ₁ : ν∈ X → fin n} {ϕ₂ : ν∈ Y → fin n} {R : X ×ν Y}
(Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕ₁ x = ϕ₂ y)) {a b : V}
(x : ν∈ insert a X) (y : ν∈ insert b Y)
(R' : R ⩁ (a, b) x y)
: inject.lam a ϕ₁ x = inject.lam b ϕ₂ y :=
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
        case or.inl p {
          have y_eq_b : y.1 = b, from p.right,
          contradiction
        },
        case or.inr p {
          cases p with x_ne_a,
          contradiction
        }
      }
    },
    case or.inr x_ne_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        cases R',
        case or.inl p {
          have x_eq_a : x.1 = a, from p.left,
          contradiction
        },
        case or.inr p {
          cases p with _ p, cases p with y_ne_b,
          contradiction
        }
      },
      case or.inr y_ne_b {
        cases R',
        case or.inl p {
          have x_eq_a : x.1 = a, from p.left,
          contradiction
        },
        case or.inr p {
          cases p with px p, cases p with py p,
          rw [dif_neg x_ne_a, dif_neg y_ne_b],
          have h : ϕ₁ (vname.erase x px) = ϕ₂ (vname.erase y py), from
            iff.mp (Rdef (vname.erase x px) (vname.erase y py)) p,
          simp [vname.erase] at *,
          rw h
        }
      }
    }
  end

def inj_Rdef_mpr {ϕ₁ : ν∈ X → fin n} {ϕ₂ : ν∈ Y → fin n} {R : X ×ν Y}
(Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕ₁ x = ϕ₂ y)) {a b : V}
(x : ν∈ insert a X) (y : ν∈ insert b Y)
(P : inject.lam a ϕ₁ x = inject.lam b ϕ₂ y)
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
        cases ϕ₂ (vname.erase y y_ne_b) with m,
        have h : 0 = nat.succ m, from fin.veq_of_eq P,
        cases h
      }
    },
    case or.inr x_ne_a {
      cases decidable.em (y.1 = b),
      case or.inl y_eq_b {
        rw [dif_neg x_ne_a, dif_pos y_eq_b] at P,
        cases ϕ₁ (vname.erase x x_ne_a) with m,
        have h : nat.succ m = 0, from fin.veq_of_eq P,
        cases h
      },
      case or.inr y_ne_b {
        rw [dif_neg x_ne_a, dif_neg y_ne_b] at P,
        right,
        existsi x_ne_a, existsi y_ne_b,
        have P : ϕ₁ (vname.erase x x_ne_a) = ϕ₂ (vname.erase y y_ne_b), from
          fin.succ.inj P,
        exact iff.mpr (Rdef (vname.erase x x_ne_a) (vname.erase y y_ne_b)) P
      }
    }
  end

def inj_Rdef {ϕ₁ : ν∈ X → fin n} {ϕ₂ : ν∈ Y → fin n} {R : X ×ν Y}
(Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕ₁ x = ϕ₂ y)) {a b : V}
(x : ν∈ insert a X) (y : ν∈ insert b Y)
: R ⩁ (a, b) x y ↔ inject.lam a ϕ₁ x = inject.lam b ϕ₂ y :=
  ⟨inj_Rdef_mp Rdef x y, inj_Rdef_mpr Rdef x y⟩

theorem inj_blah {n : ℕ} {ϕ₁ : ν∈ X → fin n} {ϕ₂ : ν∈ Y → fin n} {R : X ×ν Y}
(Rdef : ∀ (x : ν∈ X) (y : ν∈ Y), R x y ↔ (ϕ₁ x = ϕ₂ y))
(e₁ : exp X) (e₂ : exp Y)
: (e₁ ≡α⟨R⟩ e₂) ↔ (inject e₁ ϕ₁ = inject e₂ ϕ₂) :=
  begin
    induction e₁ with
      /- var -/ X x
      /- app -/ X f₁ e₁ rf re
      /- lam -/ X a e₁ r
      generalizing Y n ϕ₁ ϕ₂ R Rdef e₂,
    begin /- var -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have h : ϕ₁ x = ϕ₂ y, from iff.mp (Rdef x y) (aeq.var.prop α),
          rw h
        end,
        begin /- iff.mpr -/
          intro p,
          have h : R x y, from iff.mpr (Rdef x y) (db.var.inj p),
          exact aeq.var h
        end
      end,
      begin /- app -/
        split, repeat { intro x, cases x }
      end,
      begin /- lam -/
        split, repeat { intro x, cases x }
      end
    end,
    begin /- app -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        split, repeat { intro x, cases x },
      end,
      begin /- app -/
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have αf : f₁ ≡α⟨R⟩ f₂, from aeq.app.fun α,
          have αe : e₁ ≡α⟨R⟩ e₂, from aeq.app.arg α,
          have pf : inject f₁ ϕ₁ = inject f₂ ϕ₂, from iff.mp (rf Rdef f₂) αf,
          have pe : inject e₁ ϕ₁ = inject e₂ ϕ₂, from iff.mp (re Rdef e₂) αe,
          rw [pf, pe]
        end,
        begin /- iff.mpr -/
          intro p,
          have h : inject f₁ ϕ₁ = inject f₂ ϕ₂ ∧ inject e₁ ϕ₁ = inject e₂ ϕ₂, from
            db.app.inj p,
          have αf : f₁ ≡α⟨R⟩ f₂, from iff.mpr (rf Rdef f₂) h.1,
          have αe : e₁ ≡α⟨R⟩ e₂, from iff.mpr (re Rdef e₂) h.2,
          exact aeq.app αf αe
        end
      end,
      begin /- lam -/
        split, repeat { intro x, cases x },
      end
    end,
    begin /- lam -/
      cases e₂ with
        /- var -/ Y y
        /- app -/ Y f₂ e₂
        /- lam -/ Y b e₂,
      begin /- var -/
        split, repeat { intro x, cases x },
      end,
      begin /- app -/
        split, repeat { intro x, cases x },
      end,
      begin /- lam -/
        have Rdef' : ∀ (x : ν∈ insert a X) (y : ν∈ insert b Y), R ⩁ (a, b) x y ↔ inject.lam a ϕ₁ x = inject.lam b ϕ₂ y, from
          inj_Rdef Rdef,
        simp [inject],
        split,
        begin /- iff.mp -/
          intro α,
          have α : e₁ ≡α⟨R ⩁ (a, b)⟩ e₂, from aeq.lam.body α,
          have p : inject e₁ (inject.lam a ϕ₁) = inject e₂ (inject.lam b ϕ₂), from
            iff.mp (r Rdef' e₂) α,
          rw p
        end,
        begin /- iff.mpr -/
          intro p,
          have h : inject e₁ (inject.lam a ϕ₁) = inject e₂ (inject.lam b ϕ₂), from
            db.lam.inj p,
          have α : e₁ ≡α⟨R ⩁ (a, b)⟩ e₂, from iff.mpr (r Rdef' e₂) h,
          exact aeq.lam α
        end
      end
    end
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
