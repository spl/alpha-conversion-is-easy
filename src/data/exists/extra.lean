/-

This file contains extra definitions and theorems for `exists`.

-/

universe u

variables {A B : Sort u} {P : A → B → Prop}

protected
theorem exists.intro₂ (a : A) (b : B) : P a b → Exists (Exists ∘ P) :=
  exists.intro a ∘ exists.intro b
