/-

This file defines the `has_fresh` class.

-/

universes u v

-- A type class of operations that give a fresh element, an element that is
-- not a member of the given finite set.
--
-- The class is dependent on the element type, because that type can determine
-- how the fresh element is found.
class has_fresh (A : Type u) (B : Type u → Type v) extends has_mem A (B A) :=
  (fresh : ∀ (b : B A), Σ' a : A, a ∉ b)

-- Given `F : finset A` of `A` elements, produce a fresh `a : A` and a proof
-- that `a` is not a member of `F`.
def fresh {A : Type u} {B : Type u → Type v} [has_fresh A B]
: ∀ (b : B A), Σ' (a : A), a ∉ b :=
  has_fresh.fresh
