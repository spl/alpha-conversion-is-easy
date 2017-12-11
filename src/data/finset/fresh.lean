/-

This file defines the `fresh` class for `finset` and an instance for `nat`.

-/

import data.finset
import data.fresh

namespace nat ------------------------------------------------------------------

theorem max_zero (a : ℕ) : max a 0 = a :=
  begin
    simp [max],
    cases nat.decidable_le a 0,
    case is_true h { rw [eq_zero_of_le_zero h], refl },
    case is_false h { rw [if_neg h] }
  end

end /- namespace -/ nat --------------------------------------------------------

namespace finset ---------------------------------------------------------------

def max_nat : finset ℕ → ℕ :=
  fold max 0 id

theorem max_nat_singleton (a : ℕ) : max_nat {a} = a :=
  nat.max_zero a

theorem max_nat_insert {a : ℕ} {s : finset ℕ} (p : a ∉ s)
: max_nat (insert a s) = max a (max_nat s) :=
  fold_insert p

def max_nat_le {a : ℕ} {s : finset ℕ} : a ∈ s → a ≤ max_nat s :=
  finset.induction
    (λ (h : a ∈ ∅), false.elim (@not_mem_empty _ a h))
    (λ b s (h : b ∉ s) ih a_in_insert_b_s,
      begin
        cases decidable.em (s = ∅),
        case or.inl s_empty {
          rw [s_empty] at *,
          have R : max_nat (insert b ∅) = b, from max_nat_singleton b,
          rw [R, mem_singleton.elim_left a_in_insert_b_s]
        },
        case or.inr s_not_empty {
          rw [max_nat_insert h],
          cases mem_insert.elim_left a_in_insert_b_s with a_eq_b a_in_s,
          case or.inl a_eq_b {
            induction a_eq_b,
            exact le_max_left a (max_nat s)
          },
          case or.inr a_in_s {
            exact le_trans (ih a_in_s) (le_max_right b (max_nat s))
          }
        }
      end)
    s

-- Given a `finset` of `nat`, produce the successor of the maximum element as a
-- fresh element.
private
def fresh_nat (s : finset ℕ) : Σ' x, x ∉ s :=
  have fresh_not_mem : nat.succ (max_nat s) ∉ s, from
    assume H : nat.succ (max_nat s) ∈ s,
    have nat.succ (max_nat s) ≤ max_nat s, from max_nat_le H,
    show false, from nat.not_succ_le_self (max_nat s) this,
  psigma.mk (nat.succ (max_nat s)) fresh_not_mem

instance has_fresh : has_fresh ℕ finset :=
  { mem   := has_mem.mem
  , fresh := fresh_nat
  }

end /- namespace -/ finset -----------------------------------------------------
