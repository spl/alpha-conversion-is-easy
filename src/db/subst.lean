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

def shift (s c : ℕ) (N : fin n) : fin (n + s) :=
  if N.val < c then raise_right s N else add_right s N

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
    case var : n N {
      intro c,
      exact var (fin.shift s c N)
    },
    case app : m df de rf re {
      intro c,
      exact app (rf c) (re c)
    },
    case lam : m d r {
      intro c,
      have d : db (succ m + s) := r (succ c),
      rw succ_add m s at d,
      exact lam d
    }
  end

def shift_var : db n → db (succ n) :=
  shift 1

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
def subst.apply : subst m n → db m → db n :=
  begin
    intros F d,
    induction d generalizing n F,
    case var : m M           { exact F M },
    case app : m df de rf re { exact app (rf F) (re F) },
    case lam : m d r         { exact lam (r (subst.update F)) }
  end

variables {F : subst m n}

theorem of_var (x : fin m) : subst.apply F (var x) = F x :=
  rfl

theorem of_app (f e : db m)
: subst.apply F (app f e) = app (subst.apply F f) (subst.apply F e) :=
  rfl

theorem of_lam (e : db (succ m))
: subst.apply F (lam e) = lam (subst.apply (subst.update F) e) :=
  rfl

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
      case nat.succ : m { simp [nat.pred] }
    }
  end

theorem subst.id_eq (e : db n) : subst.apply subst.id e = e :=
  begin
    induction e,
    case var : m M         { refl },
    case app : m f e rf re { rw [of_app f e, rf, re] },
    case lam : m e r       { rw [of_lam e, subst.update_id_eq, r] }
  end

end /- namespace -/ db ---------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
