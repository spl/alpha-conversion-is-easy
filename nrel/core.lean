/-

This files contains a collection of core definitions and properties for `nrel`.

-/

import .type

open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X`, `Y`, and `Z` are finite sets of variable names.
variables {X Y Z : finset V}

namespace nrel -- ==============================================================
-- We define the core operations on `nrel`.

-- `mem` is a synonym for the function defined by `nrel` applied to arguments.
definition mem (x : ν∈ X) (y : ν∈ Y) (R : X × Y) : Prop :=
  R x y

-- Notation for `mem`.
notation p ∈ R := mem (prod.pr1 p) (prod.pr2 p) R

-- `id X` creates an identity variable relation from the single finite set `X`.
definition id (X : finset V) : X × X :=
  eq

-- `inverse R` inverts the order of the relation `R`.
definition inverse : X × Y → Y × X :=
  function.swap

-- Notation for `inverse`.
postfix ⁻¹ := inverse

-- `compose R S` combines the relations `R` and `S` to create a new relation
-- that is the composition of their underlying finite sets.
definition compose (R : X × Y) (S : Y × Z) : X × Z :=
  λ x z, ∃ y, R x y ∧ S y z

-- Notation for `compose`.
-- Source: http://www.fileformat.info/info/unicode/char/2a3e/index.htm
infixr ` ⨾ `:60 := compose

-- Lift a function to a `nrel`
definition lift (F : ν∈ X → ν∈ Y) : X × Y :=
  λ x y, (F x).1 = y.1

end nrel -- namespace ----------------------------------------------------------

-- Global attributes
attribute nrel.mem     [reducible]
attribute nrel.id      [reducible]
attribute nrel.inverse [reducible]
attribute nrel.compose [reducible]
attribute nrel.lift    [reducible]

namespace nrel -- ==============================================================
-- These are basic properties of the above definitions.

variables {R : X × Y} {S : Y × Z}

theorem mem_id : ∀ (x : ν∈ X), (x, x) ∈ id X :=
  eq.refl

variables {x : ν∈ X} {y : ν∈ Y} {z : ν∈ Z}

theorem mem_compose : (x, y) ∈ R → (y, z) ∈ S → (x, z) ∈ R ⨾ S :=
  λ x_R_y y_S_z, exists.intro y $ and.intro x_R_y y_S_z

theorem mem_inverse_iff_mem : (x, y) ∈ R ↔ (y, x) ∈ R⁻¹ :=
  iff.intro (λ H, H) (λ H, H)

end nrel -- namespace ----------------------------------------------------------

namespace nrel -- ==============================================================
-- These are properties on `id X` relations.

variables {x₁ x₂ x₃ : ν∈ X}

theorem mem_inverse_id_iff_mem_id : (x₁, x₂) ∈ (id X)⁻¹ ↔ (x₁, x₂) ∈ id X :=
  iff.intro eq.symm eq.symm

theorem mem_id_of_mem_compose_id : (x₁, x₃) ∈ id X ⨾ id X ↔ (x₁, x₃) ∈ id X :=
  have (x₁, x₃) ∈ id X ⨾ id X → (x₁, x₃) ∈ id X, from
    assume H,
    obtain (x₂ : ν∈ X) (H' : x₁ = x₂ ∧ x₂ = x₃), from  H,
    eq.trans (and.left H') (and.right H'),
  have (x₁, x₃) ∈ id X → (x₁, x₃) ∈ id X ⨾ id X, from
    assume H : x₁ = x₃,
    exists.intro x₁ (and.intro rfl H),
  iff.intro (by assumption) (by assumption)

end nrel -- namespace ----------------------------------------------------------
