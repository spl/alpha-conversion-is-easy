/-

This file contains the `vrel` `update` operation and its properties.

-/

import .type
import data.fresh
import data.sigma.extra

namespace acie ----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets

/-
The `update` operation takes `R : X ×ν Y`, erases from `R` every pair with
either `a` on the left or `b` on the right, and extends the relation with the
pair `(a, b)`.

A simple way to think about `update a b` is (using brackets for readability):

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ x ∈ X ∧ y ∈ Y ∧ R a b)

However, that does not give the proper type indexing of `R`. A closer model is:

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ R (vname.erase x px) (vname.erase y py))

But note that `px : a ≠ x` and `py : b ≠ y` are not available as arguments to
`R`. Therefore, we use an existentially quantified right alternative to include
these as propositions as well as their types as arguments.
-/

@[reducible]
protected
def update (a b : V) : X ×ν Y → insert a X ×ν insert b Y :=
  assume (R : X ×ν Y) (x : ν∈ insert a X) (y : ν∈ insert b Y),
  (x.1 = a ∧ y.1 = b) ∨
  (∃ (px : x.1 ≠ a) (py : y.1 ≠ b), R (vname.erase x px) (vname.erase y py))

-- Notation for `update`: union with minus sign.
-- Source: http://www.fileformat.info/info/unicode/char/2a41/index.htm
notation R ` ⩁ `:65 (a `, ` b) := vrel.update a b R

section ------------------------------------------------------------------------
variables {F : X →ν Y} -- Function on variable name set members

-- Lift a `vname.update` of a fresh variable to a `vrel.update`.
protected
def update.lift
(x : ν∈ insert a X) (y : ν∈ insert (fresh Y).1 Y)
: vrel.lift (vname.update a (fresh Y).1 F) x y
→ (vrel.lift F ⩁ (a, (fresh Y).1)) x y :=
  begin
    cases x with x px,
    cases y with y py,
    unfold vrel.lift vname.update,
    intro H,
    cases decidable.em (x = a) with x_eq_a x_ne_a,
    begin /- x_eq_a : x = a -/
      rw [dif_pos x_eq_a] at H,
      left, split, exact x_eq_a, rw [← H]
    end,
    begin /- x_ne_a : x ≠ a -/
      rw [dif_neg x_ne_a] at H,
      right,
      existsi x_ne_a,
      simp [vname.insert] at H,
      induction H,
      existsi vname.ne_if_mem_and_not_mem (F (vname.erase ⟨x, px⟩ x_ne_a)) (fresh Y),
      simp [vname.erase]
    end
  end

end /- section -/ --------------------------------------------------------------

end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie ------------------------------------------------------
