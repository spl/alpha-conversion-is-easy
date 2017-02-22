/-

This files contains a collection of core definitions and properties for variable
names.

-/

import .type

import data.finset
import data.finset.extra

open [notation] eq.ops
open [notation] finset
open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- Arbitrary variable names, not explicitly constrained to a finite set.
variables {a b : V}

variables {X Y : finset V}

namespace name -- ==============================================================

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
definition replace_constraint_of_eq (Y : finset V)
: a ∈ '{b} ∪ X → a = b → a ∈ '{b} ∪ Y :=

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

end name -- namespace ----------------------------------------------------------

attribute name.self_constraint          [reducible]
attribute name.erase_constraint         [reducible]
attribute name.insert_constraint        [reducible]
attribute name.replace_constraint_of_eq [reducible]

namespace name -- ==============================================================

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

-- Update a function with an extra argument and a matching result.
definition update (a b : V) (F : X ν⇒ Y) (x : ν∈ '{a} ∪ X) : ν∈ '{b} ∪ Y :=
  if P : x.1 = a then name.self b Y else name.insert b (F (name.erase x P))

-- Map the free variable set from `X` to `Y` if `x.1 ∈ Y`.
definition map_of_mem (x : ν∈ X) : x.1 ∈ Y → ν∈ Y :=
  λ px, ⟨x.1, px⟩

-- Map the free variable set from `X` to `Y` if `X ⊆ Y`.
definition map_of_subset : X ⊆ Y → ν∈ X → ν∈ Y :=
  λ P x, ⟨x.1, map_constraint P x.2⟩

end name -- namespace ----------------------------------------------------------

attribute name.self          [reducible]
attribute name.erase         [reducible]
attribute name.insert        [reducible]
attribute name.replace_of_eq [reducible]
attribute name.update        [reducible]
attribute name.map_of_mem    [reducible]
attribute name.map_of_subset [reducible]

namespace name -- ==============================================================

theorem eq_of_erase_insert {a : V} (x : ν∈ X) (x_ne_a : x.1 ≠ a)
: erase (insert a x) x_ne_a = x :=

  begin
    cases x,
    unfold [erase],
  end

-- Variables of exclusive constraints are not equal
theorem ne_of_iname_of_oname (x : ν∈ X) (x' : ν∉ X) : x.1 ≠ x'.1 :=
  finset.ne_of_mem_of_not_mem x.2 x'.2

end name -- namespace ----------------------------------------------------------
