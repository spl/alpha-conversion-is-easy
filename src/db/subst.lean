/-

This file contains substitution for `db`.

-/

import .type
import data.fin

namespace nat ------------------------------------------------------------------

variables {m n : ℕ}

def lt_add_pos_right_of_lt (p : m < n) (s : ℕ) : m < n + s :=
  match s with
    | 0        := p
    | (succ s) := lt_trans p $ nat.lt_add_of_pos_right $ zero_lt_succ s
  end

def lt_of_lt_succ_of_ne : m < succ n → m ≠ n → m < n :=
  nat.lt_of_le_and_ne ∘ le_of_lt_succ

end /- namespace -/ nat --------------------------------------------------------

namespace fin ------------------------------------------------------------------

open nat

variables {n : ℕ}

def val_gt_zero (N : fin n) : n > 0 :=
  begin
    cases N with a a_lt_n,
    cases a,
    case zero   { exact a_lt_n },
    case succ b { exact lt_trans (zero_lt_succ b) a_lt_n }
  end

def raise (s : ℕ) : fin n → fin (n + s)
  | ⟨x, x_lt_n⟩ := ⟨x, lt_add_pos_right_of_lt x_lt_n s⟩

def of_nat_add_right (s : ℕ) : fin n → fin (n + s) :=
  λ N, ⟨s, nat.lt_add_of_pos_left $ val_gt_zero N⟩

def lower (N : fin (succ n)) : N.val ≠ n → fin n :=
  begin
    cases N with a a_lt_succ_n,
    intro a_ne_n,
    split,
    exact nat.lt_of_lt_succ_of_ne a_lt_succ_n a_ne_n
  end

def shift (s c : ℕ) (N : fin n) : fin (n + s) :=
  if N.val < c then raise s N else raise s N + of_nat_add_right s N

end /- namespace -/ fin --------------------------------------------------------

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

open nat

variables {m n : ℕ} -- De Bruijn indices

def subst (m n : ℕ) : Type :=
  fin m → db n

def shift (s : ℕ) : db n → db (n + s) :=
  begin
    intro d,
    have c : ℕ := 0, -- Initial cutoff
    revert c,
    induction d,
    case var n N {
      intro c,
      exact var (fin.shift s c N)
    },
    case app m df de rf re {
      intro c,
      exact app (rf c) (re c)
    },
    case lam m d r {
      intro c,
      have d : db (succ m + s) := r (succ c),
      rw succ_add m s at d,
      exact lam d
    }
  end

def shift_var : db n → db (succ n) :=
  shift 1

protected
def subst.update_var : subst m n → subst (succ m) (succ n)
  | F M := if p : M.val = m then var (fin.of_nat n) else shift_var (F (fin.lower M p))

protected
def subst.apply : subst m n → db m → db n :=
  begin
    intros F d,
    induction d generalizing n F,
    case var m M           { exact F M },
    case app m df de rf re { exact app (rf F) (re F) },
    case lam m d r         { exact lam (r (subst.update_var F)) }
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
