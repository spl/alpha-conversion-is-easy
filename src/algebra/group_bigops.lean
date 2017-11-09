/-

This file is a port of part of algebra.group_bigops from the Lean 2 standard
library to Lean 3.

-/

import algebra.big_operators
import data.list.set
import data.finset

open list

variables {A B : Type}

def mulf [semigroup B] (f : A → B) : B → A → B :=
  λ b a, b * f a

def right_commutative_comp_right
(f : A → A → A) (g : B → A) (rcomm : right_commutative f)
: right_commutative (function.comp_right f g) :=
  λ a b₁ b₂, by apply rcomm

theorem mulf_rcomm [comm_semigroup B] (f : A → B)
: right_commutative (mulf f) :=
  right_commutative_comp_right (*) f mul_right_comm

namespace Prodl_semigroup ------------------------------------------------------

variable [semigroup B]

def Prodl_semigroup (b : B) : ∀ (l : list A) (f : A → B), B
  | []       f := b
  | (a :: l) f := list.foldl (mulf f) (f a) l

theorem Prodl_semigroup_cons (b : B) (f : A → B) (a : A) (l : list A)
: Prodl_semigroup b (a::l) f = list.foldl (mulf f) (f a) l :=
  rfl

theorem Prodl_semigroup_cons_cons (b : B) (f : A → B) (a₁ a₂ : A) (l : list A)
: Prodl_semigroup b (a₁::a₂::l) f = f a₁ * Prodl_semigroup b (a₂::l) f :=
  begin
    rw [Prodl_semigroup, Prodl_semigroup, mulf, foldl_cons],
    generalize : f a₂ = x,
    revert x,
    induction l with a l ih,
    begin -- [] case
      intro x,
      rw [foldl_nil, foldl_nil]
    end,
    begin -- (a :: l) ih case
      intro x,
      specialize ih (x * f a),
      rw [foldl_cons, foldl_cons, mul_assoc],
      exact ih
    end
  end

section decidable_eq_A ---------------------------------------------------------
variable [decidable_eq A]

theorem Prodl_semigroup_insert_insert_of_not_mem (b : B) (f : A → B)
{a₁ a₂ : A} {l : list A} (h₁ : a₂ ∉ l) (h₂ : a₁ ∉ insert a₂ l)
: Prodl_semigroup b (insert a₁ (insert a₂ l)) f = f a₁ * Prodl_semigroup b (insert a₂ l) f :=
  by rw [insert_eq_of_not_mem h₂, insert_eq_of_not_mem h₁, Prodl_semigroup_cons_cons]

end /- section -/ decidable_eq_A -----------------------------------------------

end /- namespace -/ Prodl_semigroup --------------------------------------------

namespace finset ---------------------------------------------------------------
namespace Prod_semigroup -------------------------------------------------------

variable [comm_semigroup B]

open Prodl_semigroup

private
theorem Prodl_semigroup_eq_Prodl_semigroup_of_perm
(b : B) (f : A → B) {l₁ l₂ : list A} (p : l₁ ~ l₂)
: Prodl_semigroup b l₁ f = Prodl_semigroup b l₂ f :=
  perm_induction_on p
    rfl    -- nil nil
    (λ x l₁ l₂ p ih,
     by rw [Prodl_semigroup_cons, Prodl_semigroup_cons, foldl_eq_of_perm (mulf_rcomm f) p])
    (λ x y l₁ l₂ p ih,
     by repeat {rw [Prodl_semigroup_cons, foldl_cons]};
        simp [mulf];
        apply foldl_eq_of_perm (mulf_rcomm f) p)
    (λ l₁ l₂ l₃ p₁ p₂ ih₁ ih₂,
     eq.trans ih₁ ih₂)

def Prod_semigroup (b : B) (s : finset A) (f : A → B) : B :=
  quot.lift_on s
    (λ l, Prodl_semigroup b l.val f)
    (λ l₁ l₂ p, Prodl_semigroup_eq_Prodl_semigroup_of_perm b f p)

section decidable_eq_A ---------------------------------------------------------
variable [decidable_eq A]

theorem Prod_semigroup_singleton (b : B) (f : A → B) (a : A)
: Prod_semigroup b (finset.insert a ∅) f = f a :=
  rfl

theorem Prod_semigroup_insert_insert (b : B) (f : A → B) {a₁ a₂ : A} {s : finset A}
: a₂ ∉ s → a₁ ∉ insert a₂ s
→ Prod_semigroup b (insert a₁ (insert a₂ s)) f = f a₁ * Prod_semigroup b (insert a₂ s) f :=
  quot.induction_on s
    (λ l h₁ h₂, Prodl_semigroup_insert_insert_of_not_mem b f h₁ h₂)

theorem Prod_semigroup_insert (b : B) (f : A → B) {a : A} {s : finset A}
(anins : a ∉ s) (sne : s ≠ ∅)
: Prod_semigroup b (insert a s) f = f a * Prod_semigroup b s f :=
  let ⟨a', a's⟩ := exists_mem_of_ne_empty sne in
  begin
    rw [←insert_erase a's] at *,
    rw [Prod_semigroup_insert_insert b f not_mem_erase anins]
  end

end /- section -/ decidable_eq_A -----------------------------------------------

end /- namespace -/ Prod_semigroup ---------------------------------------------
end /- namespace -/ finset -----------------------------------------------------
