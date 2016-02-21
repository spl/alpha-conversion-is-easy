/-------------------------------------------------------------------------------\

Variable names

A variable name is `n : ℕ`, an element from an infinite set of variable names
with decidable equality.

We use `names : list ℕ` as a finite subset of variable names. Given that `names`
is a finite subset of an infinite set, we are guaranteed to always be able to
find a fresh name s.t. it is not a member of `names`.

To simplify the search for a fresh name, we assume `names` is sorted by greatest
first and has no duplicates. Thus, a fresh name will always be the successor of
the list head.

\-------------------------------------------------------------------------------/

import data.nat data.list data.list.sorted
open nat list

---------------------------------------------------------------------------------

definition names := list ℕ

---------------------------------------------------------------------------------

namespace names

definition sorted := @locally_sorted ℕ gt

---------------------------------------------------------------------------------

namespace sorted

open list.locally_sorted

private lemma replace_head : ∀ {x y ns}, y > x → sorted (x :: ns) → sorted (y :: ns)
  | x y []        _      _                := !base
  | x y (w :: ns) y_gt_x (step x_gt_w IH) := step (gt.trans y_gt_x x_gt_w) IH

private lemma sorted_cons_of_gt : ∀ {x y ns}, y > x → sorted (x :: ns) → sorted (y :: x :: ns)
  | x y []        y_gt_x _                := step y_gt_x !base
  | x y (n :: ns) y_gt_x (step x_gt_n IH) := step y_gt_x (step x_gt_n IH)

private lemma hd_not_mem_of_tl : ∀ {n ns}, sorted (n :: ns) → n ∉ ns
  | n [] _ := not_mem_nil n

  | n [m] (step n_gt_m IH) :=
    assume n_mem_singleton_m : n ∈ [m],
    match iff.elim_left (mem_cons_iff n m []) n_mem_singleton_m with
      | or.inl n_eq_m    := absurd n_eq_m (ne_of_gt n_gt_m)
      | or.inr n_mem_nil := absurd n_mem_nil (not_mem_nil n)
    end

  | n (m₂ :: m₁ :: ms) (step n_gt_m2 (step m2_gt_m1 IH)) :=
    begin
      unfold mem,
      intro eq_or_mem,
      match eq_or_mem with
        | or.inl n_eq_m := absurd n_eq_m (ne_of_gt n_gt_m2)
        | or.inr n_mem_m1_ms :=
          have n_gt_m1 : n > m₁, from gt.trans n_gt_m2 m2_gt_m1,
          have n_not_mem_m1_ms : n ∉ m₁ :: ms, from
            hd_not_mem_of_tl (sorted_cons_of_gt n_gt_m1 IH),
          absurd n_mem_m1_ms n_not_mem_m1_ms
      end
    end

theorem not_mem_if_gt_hd : ∀ {x y ns}, y > x → sorted (x :: ns) → y ∉ x :: ns
  | x y [] y_gt_x _ :=
    begin
      unfold mem,
      intro eq_or_mem,
      match eq_or_mem with
        | or.inl y_eq_x    := absurd y_eq_x (ne_of_gt y_gt_x)
        | or.inr y_mem_nil := not_mem_nil x y_mem_nil
      end
    end

  | x y (m :: ms) y_gt_x (step x_gt_m IH) :=
    begin
      unfold mem,
      intro eq_or_mem,
      match eq_or_mem with
        | or.inl y_eq_x := absurd y_eq_x (ne_of_gt y_gt_x)
        | or.inr y_mem_m_ms :=
          have y_gt_m : y > m, from gt.trans y_gt_x x_gt_m,
          have y_not_mem_m_ms : y ∉ m :: ms, from
            not_mem_if_gt_hd y_gt_m IH,
          absurd y_mem_m_ms y_not_mem_m_ms
      end
    end

end sorted

---------------------------------------------------------------------------------

definition fresh : names → ℕ
  | []        := zero
  | (n :: ns) := succ n

theorem fresh.not_mem_of_sorted (n : ℕ) : ∀ ns, sorted ns → n = fresh ns → n ∉ ns
  | [] _ _ := not_mem_nil n
  | (m :: ms) sorted_m_ms n_is_fresh :=
    begin
      unfold fresh at n_is_fresh,
      rewrite n_is_fresh,
      exact (sorted.not_mem_if_gt_hd !lt_succ_self sorted_m_ms)
    end

---------------------------------------------------------------------------------

end names
