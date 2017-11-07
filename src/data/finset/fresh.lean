/-

This file defines the `fresh` class for `finset` and an instance for `nat`.

-/

import algebra.order_bigops

open nat

namespace finset -- ============================================================

-- A type class of operations that give a fresh element, an element that is
-- not a member of the given finite set.
--
-- The class is dependent on the element type, because that determines how the
-- fresh element is found.
--
-- Ideally, this class would be parameterized by the container instead of
-- specialized to `finset`, but the fact that the `∈`/`∉` operation is in the
-- type means that the class would need to be parameterized over that, too. In
-- the end, perhaps I will define a structure for all of the operations I need
-- in a container, but, for now, I'm pretty tied to `finset`.
class has_fresh (A : Type) :=
  (fresh : ∀ (F : finset A), Σ' a : A, a ∉ F)

-- Given `F : finset A` of `A` elements, produce a fresh `a : A` and a proof
-- that `a` is not a member of `F`.
definition fresh {A : Type} [has_fresh A] : ∀ F : finset A, Σ' a : A, a ∉ F :=
  has_fresh.fresh

-- Given a `finset` of `nat`, produce the successor of the maximum element as a
-- fresh element.
private
definition fresh_nat (X : finset ℕ) : Σ' x, x ∉ X :=
  have fresh_not_mem : succ (Max₀ X) ∉ X, from
    assume H : succ (Max₀ X) ∈ X,
    have succ (Max₀ X) ≤ Max₀ X, from le_Max₀ H,
    show false, from not_succ_le_self (Max₀ X) this,
  psigma.mk (succ (Max₀ X)) fresh_not_mem

instance : has_fresh ℕ :=
  { fresh := fresh_nat
  }

end finset -- namespace --------------------------------------------------------
