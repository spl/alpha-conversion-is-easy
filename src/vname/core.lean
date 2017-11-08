/-

This files contains a collection of core definitions and properties for variable
names.

-/

import .type

namespace alpha

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

namespace vname

-- Rewrite a constraint from `X` to `Y` if `X = Y`.
@[reducible]
theorem rw_constraint (H : X = Y) : a ∈ X → a ∈ Y :=
  by rw [H]; intro; assumption

-- Rewrite the free variable set from `X` to `Y` if `X = Y`.
@[reducible]
protected
theorem rw : X = Y → ν∈ X → ν∈ Y :=
  λ H x, ⟨x.1, rw_constraint H x.2⟩

@[reducible]
protected
theorem eq {x₁ x₂ : ν∈ X} (h : x₁.1 = x₂.1) : x₁ = x₂ :=
  psigma.eq h rfl

@[reducible]
protected
def insert_self (a : V) (X : vs V) : ν∈ insert a X :=
  ⟨a, vset.prop_insert_self a X⟩

-- Erase a variable from the free variable set if it is not equal to this
-- variable.
@[reducible]
protected
def erase (x : ν∈ insert a X) : x.1 ≠ a → ν∈ X :=
  λ x_ne_a, ⟨x.1, vset.prop_rm_insert_if_ne x.2 x_ne_a⟩

-- Insert a variable name into the free variable set.
@[reducible]
protected
def insert (a : V) (x : ν∈ X) : ν∈ insert a X :=
  ⟨x.1, vset.prop_insert a x.2⟩

-- Replace the free variable set of a variable name with another if the given
-- variable name equals the inserted one.
@[reducible]
def replace_of_eq : a = b → ν∈ insert b X :=
  λ a_eq_b, ⟨a, vset.prop_insert_self_if_eq X a_eq_b⟩

-- #check @vset.decidable_eq

-- Update a function on names with an extra argument and a matching result.
@[reducible]
protected
def update (a b : V) (F : X →ν Y) (x : ν∈ insert a X) : ν∈ insert b Y :=
  if P : x.1 = a then
    vname.insert_self b Y
  else
    vname.insert b (F (vname.erase x P))

-- Map the free variable set from `X` to `Y` if `x.1 ∈ Y`.
@[reducible]
def map_of_mem (x : ν∈ X) : x.1 ∈ Y → ν∈ Y :=
  λ px, ⟨x.1, px⟩

-- Map the free variable set from `X` to `Y` if `X ⊆ Y`.
@[reducible]
def map_of_subset : X ⊆ Y → ν∈ X → ν∈ Y :=
  λ P x, ⟨x.1, vset.prop_mem_of_subset P x.2⟩

theorem eq_of_erase_insert {a : V} (x : ν∈ X) (x_ne_a : x.1 ≠ a)
: vname.erase (vname.insert a x) x_ne_a = x :=
  vname.eq (by trivial)

-- Variables of exclusive constraints are not equal
theorem ne_if_mem_and_not_mem (x : ν∈ X) (x' : ν∉ X) : x.1 ≠ x'.1 :=
  vset.prop_ne_if_mem_and_not_mem x.2 x'.2

end vname

end alpha -- namespace
