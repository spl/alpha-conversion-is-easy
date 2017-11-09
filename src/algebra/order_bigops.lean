/-

This file is a port of part of algebra.order_bigops from the Lean 2 standard
library to Lean 3.

-/

import .group_bigops

variables {A B : Type}

namespace finset ---------------------------------------------------------------

section decidable_eq_A ---------------------------------------------------------

variable [decidable_eq A]

section decidable_linear_order_B -----------------------------------------------
variables [decidable_linear_order B] [has_zero B]

open Prod_semigroup

instance : comm_semigroup B :=
  { mul       := max
  , mul_assoc := max_assoc
  , mul_comm  := max_comm
  }

def Max (s : finset A) (f : A → B) : B :=
  Prod_semigroup 0 s f

def Max_singleton (f : A → B) (a : A) : Max {a} f = f a :=
  Prod_semigroup_singleton _ _ _

theorem Max_insert (f : A → B) {a : A} {s : finset A} (anins : a ∉ s) (sne : s ≠ ∅)
: Max (insert a s) f = max (f a) (Max s f) :=
  Prod_semigroup_insert _ _ anins sne

def le_Max (f : A → B) {a : A} {s : finset A} : a ∈ s → f a ≤ Max s f :=
  finset.induction
    (λ (H : a ∈ ∅), false.elim (@not_mem_empty _ a H))
    (λ a' s' (H : a' ∉ s') ih a_in_insert_a'_s,
     begin
       cases decidable.em (s' = ∅) with s'_empty s'_not_empty,
       begin /- s'_empty : s' = ∅ -/
         rw [s'_empty] at *,
         have R : Max (insert a' ∅) f = f a', from Max_singleton f a',
         rw [R, mem_singleton.elim_left a_in_insert_a'_s],
       end,
       begin /- s'_not_empty : s' ≠ ∅ -/
         rw [Max_insert f H s'_not_empty],
         cases mem_insert.elim_left a_in_insert_a'_s with a_eq_a' a_in_s',
         begin /- a_eq_a' : a = a' -/
           rw [a_eq_a'],
           exact le_max_left (f a') (Max s' f)
         end,
         begin /- a_in_s' : a ∈ s' -/
           exact le_trans (ih a_in_s') (le_max_right (f a') (Max s' f))
         end
       end
     end)
    s

end /- section -/ decidable_linear_order_B -------------------------------------

end /- section -/ decidable_eq_A -----------------------------------------------

section decidable_linear_order_A -----------------------------------------------
variables [decidable_linear_order A] [has_zero A]

def Max₀ (s : finset A) : A :=
  Max s id

def le_Max₀ {a : A} {s : finset A} : a ∈ s → a ≤ Max₀ s :=
  le_Max id

end /- section -/ decidable_linear_order_A -------------------------------------

end /- namespace -/ finset -----------------------------------------------------
