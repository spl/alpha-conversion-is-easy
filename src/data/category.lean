/-

This file contains definitions and theorems for `category`.

Some of this was adapted from work by Simon Hudon.
Source: https://github.com/unitb/lean-lib/blob/master/src/util/category.lean

-/

universes u v

variables {O : Sort u} -- Type of objects in a category

/-
A class for homomorphisms with composition.
-/
class has_comp (H : O → O → Type v) :=
  (comp : ∀ {a b c : O}, H b c → H a b → H a c)

instance has_comp.arrow : has_comp (→) :=
  { comp := @function.comp
  }

-- Convenient composition notation.
infixr ` ∘ ` := has_comp.comp _

/-
A class for categories uniquely identified by the homomorphism `H` (i.e. the
arrow). The object type `O` is implicit.

We use a setoid rather than `=` for equalities that do not exactly fit the `eq`
type.
-/
class category (H : O → O → Type v) [∀ a b, setoid (H a b)] extends has_comp H :=
  (id       : ∀ {a : O}, H a a) -- Identity
  (left_id  : ∀ {a b : O} (f : H a b), id ∘ f ≈ f) -- Left unit of identity
  (right_id : ∀ {a b : O} (f : H a b), f ∘ id ≈ f) -- Right unit of identity
  (assoc    : ∀ {a b c d : O} (h : H c d) (g : H b c) (f : H a b), h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f) -- Associativity

instance category.arrow : category (→) :=
  { comp     := @function.comp
  , id       := @id
  , left_id  := λ a b, function.equiv.refl
  , right_id := λ a b, function.equiv.refl
  , assoc    := λ a b c d h g f, function.equiv.refl (h ∘ (g ∘ f))
  }
