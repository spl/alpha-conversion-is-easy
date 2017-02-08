/-

This file contains type definitions for variables (not) in finite sets.

-/

import data.finset
import data.finset.extra

open [notation] eq.ops
open [notation] finset
open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

/-
`cvar X` is a constrained variable name (i.e. an element of `V`). It is
constrained to be a member of the finite set of variable names `X`.

Since the underlying type is `sigma`, we use the notation `⟨x, px⟩` to create a
`cvar X` with the variable, `x : V`, and its proof of membership, `px : x ∈ X`.
-/

definition cvar (X : finset V) : Type :=
  Σ x : V, x ∈ X

/-
`fvar X` is a fresh variable name: an element of `V` but _not_ a member of `X`.

This is the complement to `cvar`. It is used for variables fresh wrt a `finset`.

Since the underlying type is `sigma`, we use the notation `⟨x, px⟩` to create a
`fvar X` with the variable, `x : V`, and its proof of membership, `px : x ∈ X`.
-/

definition fvar (X : finset V) : Type :=
  Σ x : V, x ∉ X

-- Convenient notation for the above.
prefix `ν∈ `:40 := cvar  -- \nu\in
prefix `ν∉ `:40 := fvar  -- \nu\notin

-- Arbitrary variable names, not explicitly constrained to a finite set.
variables {a b : V}

variables {X Y : finset V}

namespace cvar -- ==============================================================

definition self_constraint : ∀ (a : V) (X : finset V), a ∈ '{a} ∪ X :=
  finset.mem_insert

-- Erase a variable from the free variable set if it is not equal to this
-- variable.
definition erase_constraint : a ∈ '{b} ∪ X → a ≠ b → a ∈ X :=
  finset.mem_of_mem_insert_of_ne

-- Insert a variable name into the free variable set of a constraint.
definition insert_constraint : ∀ b : V, a ∈ X → a ∈ '{b} ∪ X :=
  finset.mem_insert_of_mem

-- Make a new constraint for another free variable set if the given variable
-- name equals the inserted one.
definition replace_constraint_of_eq (Y : finset V) : a ∈ '{b} ∪ X → a = b → a ∈ '{b} ∪ Y :=
  assume pa a_eq_b,
  begin
    generalize self_constraint a Y,
    intro p,
    rewrite a_eq_b at p{2},
    exact p
  end

-- Convert a constraint of X to one of which `X` is a subset, `Y`.
definition map_constraint : X ⊆ Y → a ∈ X → a ∈ Y :=
  finset.mem_of_subset_of_mem

end cvar -- namespace ----------------------------------------------------------

attribute cvar.self_constraint          [reducible]
attribute cvar.erase_constraint         [reducible]
attribute cvar.insert_constraint        [reducible]
attribute cvar.replace_constraint_of_eq [reducible]

namespace cvar -- ==============================================================

protected
definition eq {x₁ : ν∈ X} {x₂ : ν∈ X} : x₁.1 = x₂.1 → x₁ = x₂ :=
  λ e, eq_of_heq $
    sigma.heq !heq.refl (heq_of_eq e) (hproof_irrel (by rewrite e) _ _)

definition self (a : V) (X : finset V) : ν∈ '{a} ∪ X :=
  ⟨a, self_constraint a X⟩

-- Erase a variable from the free variable set if it is not equal to this
-- variable.
definition erase (x : ν∈ '{a} ∪ X) : x.1 ≠ a → ν∈ X :=
  λ x_ne_a, ⟨x.1, erase_constraint x.2 x_ne_a⟩

-- Insert a variable name into the free variable set.
definition insert (a : V) (x : ν∈ X) : ν∈ '{a} ∪ X :=
  ⟨x.1, insert_constraint a x.2⟩

-- Replace the free variable set of a variable name with another if the given
-- variable name equals the inserted one.
definition replace_of_eq (Y : finset V) (x : ν∈ '{a} ∪ X) : x.1 = a → ν∈ '{a} ∪ Y :=
  λ x_eq_a, ⟨x.1, replace_constraint_of_eq Y x.2 x_eq_a⟩

-- Map the free variable set from `X` to `Y` if `x.1 ∈ Y`.
definition map_of_mem (x : ν∈ X) : x.1 ∈ Y → ν∈ Y :=
  λ px, ⟨x.1, px⟩

-- Map the free variable set from `X` to `Y` if `X ⊆ Y`.
definition map_of_subset : X ⊆ Y → ν∈ X → ν∈ Y :=
  λ P x, ⟨x.1, map_constraint P x.2⟩

end cvar -- namespace ----------------------------------------------------------

attribute cvar.self          [reducible]
attribute cvar.erase         [reducible]
attribute cvar.insert        [reducible]
attribute cvar.replace_of_eq [reducible]
attribute cvar.map_of_mem   [reducible]
attribute cvar.map_of_subset [reducible]

namespace cvar -- ==============================================================

theorem eq_of_erase_insert {a : V} (x : ν∈ X) (x_ne_a : x.1 ≠ a)
: erase (insert a x) x_ne_a = x :=

  begin
    cases x,
    unfold [erase],
  end

end cvar -- namespace ----------------------------------------------------------
