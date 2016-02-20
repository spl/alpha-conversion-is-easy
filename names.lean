/-------------------------------------------------------------------------------\
  Variable names
\-------------------------------------------------------------------------------/

import data.nat
open nat

---------------------------------------------------------------------------------

inductive names : Type :=
  | name : ℕ → names
  | cons : ℕ → names → names

namespace names

definition mem (x : ℕ) : names → Prop
  | (name n)    := n = x
  | (cons n ns) := if n < x then mem ns else n = x

inductive sorted : names → Prop :=
  | base  : ∀ n,                                          sorted (name n)
  | step₁ : ∀ {n₁ n₂},    n₁ < n₂                       → sorted (cons n₂ (name n₁))
  | step₂ : ∀ {n₁ n₂ ns}, n₁ < n₂ → sorted (cons n₁ ns) → sorted (cons n₂ (cons n₁ ns))

open sorted

lemma sorted_replace_head : ∀ {x y ns}, x < y → sorted (cons x ns) → sorted (cons y ns)
  | x y (name w)    x_lt_y (step₁ w_lt_x)    := step₁ (lt.trans w_lt_x x_lt_y)
  | x y (cons w ns) x_lt_y (step₂ w_lt_x IH) := step₂ (lt.trans w_lt_x x_lt_y) IH

lemma sorted_cons_of_gt_of_sorted : ∀ {x y ns}, x < y → sorted (cons x ns) → sorted (cons y (cons x ns))
  | _ _ (name _)   x_lt_y (step₁ w_lt_x)    := step₂ x_lt_y (step₁ w_lt_x)
  | _ _ (cons _ _) x_lt_y (step₂ w_lt_x IH) := step₂ x_lt_y (sorted_cons_of_gt_of_sorted w_lt_x IH)

lemma not_mem_of_sorted_cons : ∀ {n ns}, sorted (cons n ns) → ¬ mem n ns
  | m (name n) (step₁ n_lt_m) := by unfold mem; exact (ne_of_lt n_lt_m)

  | m (cons n₂ (name n₁)) (step₂ n2_lt_m S) :=
    begin
      unfold mem,
      rewrite (if_pos n2_lt_m),
      unfold mem,
      cases S,  -- Generates: a : n₁ < n₂
      exact (ne_of_lt (lt.trans a n2_lt_m))
    end

  | m (cons n₂ (cons n₁ ns)) (step₂ n2_lt_m S) :=
    begin
      cases S,  -- Generates: a : n₁ < n₂, a_1 : sorted (cons n₁ ns)
      unfold mem,
      rewrite (if_pos n2_lt_m),
      exact (not_mem_of_sorted_cons (sorted_cons_of_gt_of_sorted (lt.trans a n2_lt_m) a_1))
    end

lemma not_mem_of_gt2 {x y ns} (x_lt_y : x < y) (S : sorted (cons x ns)) : ¬ mem y ns :=
  not_mem_of_sorted_cons (sorted_replace_head x_lt_y S)

theorem not_mem_of_gt : ∀ {x y ns}, x < y → sorted (cons x ns) → ¬ mem y (cons x ns)
  | x y (name n) x_lt_y (step₁ n_lt_x) :=
    begin
      unfold mem,
      rewrite (if_pos x_lt_y),
      unfold mem,
      exact (ne_of_lt (lt.trans n_lt_x x_lt_y))
    end
  | x y (cons n ns) x_lt_y (step₂ n_lt_x IH) :=
    begin
      unfold mem,
      rewrite (if_pos x_lt_y),
      unfold mem,
      rewrite (if_pos (lt.trans n_lt_x x_lt_y)),
      exact (not_mem_of_gt2 (lt.trans n_lt_x x_lt_y) IH)
    end

definition fresh : names → ℕ
  | (name n)    := succ n
  | (cons n ns) := succ n

theorem fresh_not_mem (x : ℕ) : ∀ ns, sorted ns → x = fresh ns → ¬ mem x ns
  | (name n) _ x_is_fresh :=
    begin
      unfold fresh at x_is_fresh,
      rewrite x_is_fresh,
      unfold mem,
      exact (ne.symm succ_ne_self)
    end
  | (cons n ns) ns_sorted x_is_fresh :=
    begin
      unfold fresh at x_is_fresh,
      rewrite x_is_fresh,
      exact (not_mem_of_gt (self_lt_succ n) ns_sorted),
    end

end names
