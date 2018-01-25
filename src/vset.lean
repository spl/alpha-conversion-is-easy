/-

This files contains the `vset` type class definition and instances.

-/

import data.fresh

universes u v

namespace acie -----------------------------------------------------------------

/-
The type class `vset V S` defines the requirements for a finite set `S` of
variable names allocated from the infinite set of variable names `V` with
decidable equality.
-/

class vset (S : Type u → Type v) (V : Type u) [decidable_eq V]
extends has_fresh V S
      , has_emptyc (S V)
      , has_insert V (S V)
      , has_subset (S V) :=
  (prop_insert_self           : ∀ (a : V) (s : S V), a ∈ insert a s)
  (prop_insert                : ∀ {a : V} (b : V) {s : S V}, a ∈ s → a ∈ insert b s)
  (prop_insert_idem           : ∀ (a : V) (s : S V), insert a (insert a s) = insert a s)
  (prop_insert_comm           : ∀ (a b : V) (s : S V), insert a (insert b s) = insert b (insert a s))
  (prop_rm_insert_if_ne       : ∀ {a b : V} {s : S V}, b ∈ insert a s → b ≠ a → b ∈ s)
  (prop_mem_of_subset         : ∀ {a : V} {s₁ s₂ : S V}, s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂)
  (prop_ne_if_mem_and_not_mem : ∀ {a b : V} {s : S V}, a ∈ s → b ∉ s → a ≠ b)
  (prop_subset_refl           : ∀ (s : S V), s ⊆ s)
  (prop_subset_trans          : ∀ {s₁ s₂ s₃ : S V}, s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃)
  (prop_insert_of_subset      : ∀ (a : V) {s₁ s₂ : S V}, s₁ ⊆ s₂ → insert a s₁ ⊆ insert a s₂)
  (prop_subset_insert_self    : ∀ (a : V) (s : S V), s ⊆ insert a s)

namespace vset -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {S : Type → Type} [vset S V] -- Type of variable name sets
variables {a b : V} -- Variable names

-- Make a new constraint for another free variable set if the given variable
-- name equals the inserted one.
theorem prop_insert_self_if_eq (s : S V) (p : a = b) : a ∈ insert b s :=
  by rw [p]; exact vset.prop_insert_self b s

theorem prop_subset_of_insert_comm (a b : V) (s : S V)
: insert a (insert b s) ⊆ insert b (insert a s) :=
  calc
    insert a (insert b s)
        = insert b (insert a s) : prop_insert_comm a b s
    ... ⊆ insert b (insert a s) : prop_subset_refl (insert b (insert a s))

theorem prop_subset_of_insert_comm_refl (a : V) (s : S V)
: prop_subset_of_insert_comm a a s = prop_subset_refl (insert a (insert a s)) :=
  rfl

end /- namespace -/ vset -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
