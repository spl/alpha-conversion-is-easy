/-

This files contains a collection of core definitions and properties for `vrel`.

-/

import .type

open [notation] function
open [notation] sigma.ops

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

-- `X`, `Y`, and `Z` are finite sets of variable names.
variables {X Y Z : finset V}

namespace vrel -- ==============================================================
-- We define the core operations on `vrel`.

-- `mem` is a synonym for the function defined by `vrel` applied to arguments.
definition mem (x : ν∈ X) (y : ν∈ Y) (R : vrel X Y) : Prop :=
  R x y

-- Convenient notation for `mem`.
notation `⟪` x `, ` y `, ` R `⟫` := mem x y R
notation `⟪` R `⟫` := mem _ _ R  -- if the member properties can be inferred

-- `id X` creates an identity variable relation from the single finite set `X`.
definition id (X : finset V) : vrel X X :=
  eq

-- `inverse R` inverts the order of the relation `R`.
definition inverse : vrel X Y → vrel Y X :=
  function.swap

-- `compose R S` combines the relations `R` and `S` to create a new relation
-- that is the composition of their underlying finite sets.
definition compose (R : vrel X Y) (S : vrel Y Z) : vrel X Z :=
  λ x z, ∃ y, R x y ∧ S y z

-- Convenient notation for `compose`.
-- Source: http://www.fileformat.info/info/unicode/char/2a3e/index.htm
notation R ` ⨾ `:60 S := compose R S

-- Lift a function to a `vrel`
definition lift (F : ν∈ X → ν∈ Y) : vrel X Y :=
  λ x y, (F x).1 = y.1

end vrel -- namespace ----------------------------------------------------------

-- Global attributes
attribute vrel.mem     [reducible]
attribute vrel.id      [reducible]
attribute vrel.inverse [reducible]
attribute vrel.compose [reducible]

namespace vrel -- ==============================================================
-- These are basic properties of the above definitions.

variables {R : vrel X Y} {S : vrel Y Z}

theorem mem_id : ∀ (x : ν∈ X), ⟪x, x, id X⟫ :=
  eq.refl

variables {x : ν∈ X} {y : ν∈ Y} {z : ν∈ Z}

theorem mem_compose : ⟪x, y, R⟫ → ⟪y, z, S⟫ → ⟪x, z, R ⨾ S⟫ :=
  λ x_R_y y_S_z, exists.intro y $ and.intro x_R_y y_S_z

theorem mem_inverse_iff_mem : (⟪x, y, R⟫ ↔ ⟪y, x, inverse R⟫) :=
  iff.intro (λ H, H) (λ H, H)

end vrel -- namespace ----------------------------------------------------------

namespace vrel -- ==============================================================
-- These are properties on `id X` relations.

variables {x₁ x₂ x₃ : ν∈ X}

theorem mem_inverse_id_iff_mem_id : ⟪x₁, x₂, inverse (id X)⟫ ↔ ⟪x₁, x₂, id X⟫ :=
  iff.intro eq.symm eq.symm

theorem mem_id_of_mem_compose_id : ⟪x₁, x₃, id X ⨾ id X⟫ ↔ ⟪x₁, x₃, id X⟫ :=
  have ⟪id X ⨾ id X⟫ → ⟪id X⟫, from
    assume H,
    obtain (x₂ : ν∈ X) (H' : x₁ = x₂ ∧ x₂ = x₃), from  H,
    eq.trans (and.left H') (and.right H'),
  have ⟪id X⟫ → ⟪id X ⨾ id X⟫, from
    assume H : x₁ = x₃,
    exists.intro x₁ (and.intro rfl H),
  iff.intro (by assumption) (by assumption)

end vrel -- namespace ----------------------------------------------------------
