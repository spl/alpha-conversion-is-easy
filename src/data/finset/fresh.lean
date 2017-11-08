/-

This file defines the `fresh` class for `finset` and an instance for `nat`.

-/

import algebra.order_bigops
import data.fresh

open nat

namespace finset -- ============================================================

-- Given a `finset` of `nat`, produce the successor of the maximum element as a
-- fresh element.
private
def fresh_nat (X : finset ℕ) : Σ' x, x ∉ X :=
  have fresh_not_mem : succ (Max₀ X) ∉ X, from
    assume H : succ (Max₀ X) ∈ X,
    have succ (Max₀ X) ≤ Max₀ X, from le_Max₀ H,
    show false, from not_succ_le_self (Max₀ X) this,
  psigma.mk (succ (Max₀ X)) fresh_not_mem

instance has_fresh : has_fresh ℕ finset :=
  { mem   := finset.mem
  , fresh := fresh_nat
  }

end finset -- namespace --------------------------------------------------------
