/-

This file contains the `db` inductive data type for De Bruijn terms.

-/

namespace acie -----------------------------------------------------------------

open nat

inductive db : ℕ → Type
  | var : Π {n : ℕ}, fin n       → db n  -- variable
  | app : Π {n : ℕ}, db n → db n → db n  -- application
  | lam : Π {n : ℕ}, db (succ n) → db n  -- lambda abstraction

namespace db -------------------------------------------------------------------

def repr : ∀ {n : ℕ}, db n → string
  | n (var N)   := _root_.repr N
  | n (app f e) := "(" ++ repr f ++ " " ++ repr e ++ ")"
  | n (lam e)   := "(λ " ++ repr e ++ ")"

instance has_repr (n : ℕ) : has_repr (db n) :=
  ⟨@repr n⟩

end /- namespace -/ db ---------------------------------------------------------

end /- namespace -/ acie -------------------------------------------------------
