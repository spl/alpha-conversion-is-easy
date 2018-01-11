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

@[simp]
def raise_right (s : ℕ) : fin n → fin (n + s)
  | ⟨m, m_lt_n⟩ := ⟨m, lt_add_pos_right_of_lt m_lt_n s⟩

@[simp]
def add_right (s : ℕ) : fin n → fin (n + s)
  | ⟨m, m_lt_n⟩ := ⟨m + s, nat.add_lt_add_right m_lt_n s⟩

@[simp]
theorem succ_eq_add_right_1 {N : fin n} : add_right 1 N = fin.succ N :=
  rfl

def shift (s c : ℕ) (N : fin n) : fin (n + s) :=
  if N.val < c then raise_right s N else add_right s N

@[simp]
theorem succ_eq_shift_1_0 {N : fin n} : shift 1 0 N = fin.succ N :=
  rfl

-- TODO
-- theorem shift_s_0_eq_shift_s_1 {N : fin n} : shift s 1 N = shift s 0 N

end /- namespace -/ fin --------------------------------------------------------

namespace acie -----------------------------------------------------------------
namespace db -------------------------------------------------------------------

open nat

variables {m n : ℕ} -- De Bruijn indices

def subst (m n : ℕ) : Type :=
  fin m → db n

@[inline]
def shift.succ_add {s n : ℕ} : db (succ n + s) → db (succ (n + s)) :=
  eq.mpr (eq.rec (eq.refl (db (succ (n + s)))) (eq.symm (nat.succ_add n s)))

def shift (s : ℕ) : ∀ {n : ℕ}, ℕ → db n → db (n + s)
  | n c (var N)   := var (fin.shift s c N)
  | n c (app f e) := app (shift c f) (shift c e)
  | n c (lam e)   := lam (db.shift.succ_add (shift (succ c) e))

def shift_var : db n → db (succ n) :=
  shift 1 0

-- add_key_equivalence shift_var shift

protected
def subst.id : subst n n :=
  var

protected
def subst.update (F : subst m n) : subst (succ m) (succ n) :=
  λ (M : fin (succ m)),
  if p : M = 0 then
    var 0
  else
    shift_var (F (fin.pred M p))

protected
def subst.apply : ∀ {m n : ℕ}, subst m n → db m → db n
  | m n F (var M)   := F M
  | m n F (app f e) := app (subst.apply F f) (subst.apply F e)
  | m n F (lam e)   := lam (subst.apply (subst.update F) e)

theorem subst.update_id_eq : subst.update (@subst.id n) = @subst.id (succ n) :=
  begin
    funext M,
    simp [subst.update],
    cases decidable.em (M = 0),
    case or.inl : M_eq_0 {
      rw [dif_pos M_eq_0, M_eq_0],
      refl
    },
    case or.inr : M_ne_0 {
      rw dif_neg M_ne_0,
      simp [subst.id, shift_var, shift, fin.shift],
      rw if_neg (nat.not_lt_zero (fin.pred M M_ne_0).val),
      cases M with m m_lt_succ_n,
      simp [fin.pred],
      cases m,
      case nat.zero     { cases ne.irrefl (fin.vne_of_ne M_ne_0) },
      case nat.succ : m { simp [nat.pred_succ], refl }
    }
  end

theorem subst.id_eq (e : db n) : subst.apply subst.id e = e :=
  begin
    induction e,
    case var : m M         { refl },
    case app : m f e rf re { rw [subst.apply, rf, re] },
    case lam : m e r       { rw [subst.apply, subst.update_id_eq, r] }
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
