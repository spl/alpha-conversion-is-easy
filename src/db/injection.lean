/-

This file contains the injection of `db` into `exp`.

-/

import .type
import aeq

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

theorem inj_blah (ϕ₁ : ν∈ X → fin n) (ϕ₂ : ν∈ Y → fin n) (e₁ : exp X) (e₂ : exp Y)
: (e₁ ≡α⟨blah ϕ₁ ϕ₂⟩ e₂) ↔ (inject e₁ ϕ₁ = inject e₂ ϕ₂) :=
  begin
    induction e₁ with
      /- var -/ X x
      /- app -/ X f₁ e₁ rf re
      /- lam -/ X a e₁ r
      generalizing Y ϕ₁ ϕ₂ e₂,
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
          have h : ϕ₁ x = ϕ₂ y, from aeq.var.prop α,
          rw [h]
        end,
        begin /- iff.mpr -/
          intro p,
          have h : ϕ₁ x = ϕ₂ y, from db.var.inj p,
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
          have αf : f₁ ≡α⟨blah ϕ₁ ϕ₂⟩ f₂, from aeq.app.fun α,
          have αe : e₁ ≡α⟨blah ϕ₁ ϕ₂⟩ e₂, from aeq.app.arg α,
          have pf : inject f₁ ϕ₁ = inject f₂ ϕ₂, from iff.mp (rf ϕ₁ ϕ₂ f₂) αf,
          have pe : inject e₁ ϕ₁ = inject e₂ ϕ₂, from iff.mp (re ϕ₁ ϕ₂ e₂) αe,
          rw [pf, pe]
        end,
        begin /- iff.mpr -/
          intro p,
          have h : inject f₁ ϕ₁ = inject f₂ ϕ₂ ∧ inject e₁ ϕ₁ = inject e₂ ϕ₂, from
            db.app.inj p,
          have αf : f₁ ≡α⟨blah ϕ₁ ϕ₂⟩ f₂, from iff.mpr (rf ϕ₁ ϕ₂ f₂) h.1,
          have αe : e₁ ≡α⟨blah ϕ₁ ϕ₂⟩ e₂, from iff.mpr (re ϕ₁ ϕ₂ e₂) h.2,
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
      end
    end
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
