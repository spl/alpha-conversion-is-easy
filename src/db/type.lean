/-

This file contains the `db` inductive data type for De Bruijn terms.

-/

namespace acie -----------------------------------------------------------------

open nat

inductive db : ℕ → Type
  | var : Π {n : ℕ}, fin n       → db n  -- variable
  | app : Π {n : ℕ}, db n → db n → db n  -- application
  | lam : Π {n : ℕ}, db (succ n) → db n  -- lambda abstraction

end /- namespace -/ acie -------------------------------------------------------
