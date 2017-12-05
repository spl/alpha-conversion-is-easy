/-

This file contains the injection of `db` into `exp`.

-/

import .type
import exp

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X : vs V} -- Variable name sets
variables {n : ℕ} -- De Bruijn indexes

def inject_lam (a : V) (ϕ : ν∈ X → fin n) (x : ν∈ (insert a X)) : fin (nat.succ n) :=
  if p : x.1 = a then fin.of_nat 0 else fin.succ $ ϕ $ vname.erase x p

def inject : ∀ {X : vs V}, exp X → ∀ {n : ℕ}, (ν∈ X → fin n) → db n
  | X (exp.var x)              n ϕ := db.var $ ϕ x
  | X (exp.app f e)            n ϕ := db.app (inject f ϕ) (inject e ϕ)
  | X (@exp.lam _ _ _ _ _ a e) n ϕ := db.lam $ inject e $ inject_lam a ϕ

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
