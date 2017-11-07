/-

This file contains the `nrel` `update` operation and its properties.

-/

import .comp
import .inv

import data.finset.fresh
import data.sigma.extra

-- `V` is the type of an infinite set of variable names with decidable equality.
variables {V : Type} [decidable_eq V]

variables {X Y Z : finset V}

variables {a b c : V}

namespace alpha

namespace nrel -- ==============================================================

/-
The `update` operation takes `R : X ×ν Y`, erases from `R` every pair with
either `a` on the left or `b` on the right, and extends the relation with the
pair `(a, b)`.

A simple way to think about `update a b` is (using brackets for readability):

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ x ∈ X ∧ y ∈ Y ∧ R a b)

However, that does not give the proper type indexing of `R`. A closer model is:

  (a = x ∧ b = y) ∨ (a ≠ x ∧ b ≠ y ∧ R (name.erase x px) (name.erase y py))

But note that `px : a ≠ x` and `py : b ≠ y` are not available as arguments to
`R`. Therefore, we use an existentially quantified right alternative to include
these as propositions as well as their types as arguments.
-/

@[reducible]
definition update (a b : V) : X ×ν Y → insert a X ×ν insert b Y :=
  assume (R : X ×ν Y) (x : ν∈ insert a X) (y : ν∈ insert b Y),
  (x.1 = a ∧ y.1 = b) ∨
  (∃ (px : x.1 ≠ a) (py : y.1 ≠ b), R (name.erase x px) (name.erase y py))

-- Notation for `update`: union with minus sign.
-- Source: http://www.fileformat.info/info/unicode/char/2a41/index.htm
notation R ` ⩁ `:65 (a `, ` b) := update a b R

section

variables [finset.has_fresh V] {F : X ν⇒ Y}

-- Lift a `name.update` of a fresh variable to a `nrel.update`.
protected
definition update.lift
(x : ν∈ insert a X) (y : ν∈ insert (finset.fresh Y).1 Y)
: nrel.lift (name.update a (finset.fresh Y).1 F) x y
→ (nrel.lift F ⩁ (a, (finset.fresh Y).1)) x y :=
  begin
    cases x with x px,
    cases y with y py,
    unfold nrel.lift name.update,
    intro H,
    cases decidable.em (x = a) with x_eq_a x_ne_a,
    begin /- x_eq_a : x = a -/
      rw [dif_pos x_eq_a] at H,
      left, split, exact x_eq_a, rw [← H]
    end,
    begin /- x_ne_a : x ≠ a -/
      rw [dif_neg x_ne_a] at H,
      simp [psigma.mk_eq_mk_iff] at *,
      induction H,
      right,
      split,
      begin
        existsi name.ne_of_iname_of_oname (F (name.erase ⟨x, px⟩ x_ne_a)) (finset.fresh Y),
        simp
      end,
      begin
        exact x_ne_a
      end
    end
  end

end

end nrel -- namespace

end alpha -- namespace
