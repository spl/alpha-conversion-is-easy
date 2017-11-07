/-

This files contains a collection of core definitions and properties for variable
names.

-/

import .type
import data.finset.extra

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- Arbitrary variable names, not explicitly constrained to a finite set.
variables {a b : V}

variables {X Y : finset V}

namespace alpha

namespace name -- ==============================================================

@[reducible]
def self_constraint : a ∈ finset.insert a X :=
  finset.mem_insert_self

-- Erase a variable from the free variable set if it is not equal to this
-- variable.
@[reducible]
def erase_constraint : a ∈ finset.insert b X → a ≠ b → a ∈ X :=
  finset.mem_of_mem_insert_of_ne

-- Insert a variable name into the free variable set of a constraint.
@[reducible]
def insert_constraint : a ∈ X → a ∈ finset.insert b X :=
  finset.mem_insert_of_mem

-- Make a new constraint for another free variable set if the given variable
-- name equals the inserted one.
@[reducible]
def replace_constraint_of_eq (H : a = b) : a ∈ finset.insert b Y :=
  by rw [H]; exact self_constraint

-- Rewrite a constraint from `X` to `Y` if `X = Y`.
@[reducible]
def rw_constraint (H : X = Y) : a ∈ X → a ∈ Y :=
  by rw [H]; intro; assumption

-- Convert a constraint of X to one of which `X` is a subset, `Y`.
@[reducible]
def map_constraint : X ⊆ Y → a ∈ X → a ∈ Y :=
  finset.mem_of_subset_of_mem

-- Rewrite the free variable set from `X` to `Y` if `X = Y`.
@[reducible]
protected
def rw : X = Y → ν∈ X → ν∈ Y :=
  λ H x, ⟨x.1, rw_constraint H x.2⟩

@[reducible]
protected
def eq {x₁ x₂ : ν∈ X} (h : x₁.1 = x₂.1) : x₁ = x₂ :=
  psigma.eq h rfl

@[reducible]
def self (a : V) (X : finset V) : ν∈ finset.insert a X :=
  ⟨a, self_constraint⟩

-- Erase a variable from the free variable set if it is not equal to this
-- variable.
@[reducible]
def erase (x : ν∈ finset.insert a X) : x.1 ≠ a → ν∈ X :=
  λ x_ne_a, ⟨x.1, erase_constraint x.2 x_ne_a⟩

-- Insert a variable name into the free variable set.
@[reducible]
def insert (a : V) (x : ν∈ X) : ν∈ finset.insert a X :=
  ⟨x.1, insert_constraint x.2⟩

-- Replace the free variable set of a variable name with another if the given
-- variable name equals the inserted one.
@[reducible]
def replace_of_eq : a = b → ν∈ finset.insert b X :=
  λ a_eq_b, ⟨a, replace_constraint_of_eq a_eq_b⟩

-- Update a function on names with an extra argument and a matching result.
@[reducible]
def update (a b : V) (F : X ν⇒ Y) (x : ν∈ finset.insert a X)
: ν∈ finset.insert b Y :=
  if P : x.1 = a then self b Y else insert b (F (erase x P))

-- Map the free variable set from `X` to `Y` if `x.1 ∈ Y`.
@[reducible]
def map_of_mem (x : ν∈ X) : x.1 ∈ Y → ν∈ Y :=
  λ px, ⟨x.1, px⟩

-- Map the free variable set from `X` to `Y` if `X ⊆ Y`.
@[reducible]
def map_of_subset : X ⊆ Y → ν∈ X → ν∈ Y :=
  λ P x, ⟨x.1, map_constraint P x.2⟩

theorem eq_of_erase_insert {a : V} (x : ν∈ X) (x_ne_a : x.1 ≠ a)
: erase (insert a x) x_ne_a = x :=
  name.eq (by trivial)

-- Variables of exclusive constraints are not equal
theorem ne_of_iname_of_oname (x : ν∈ X) (x' : ν∉ X) : x.1 ≠ x'.1 :=
  finset.ne_of_mem_of_not_mem x.2 x'.2

end name -- namespace ----------------------------------------------------------

end alpha -- namespace
