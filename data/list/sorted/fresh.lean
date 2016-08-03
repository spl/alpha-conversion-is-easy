import data.list.sorted.basic
import data.list.sorted.mem
import data.nat.gt_properties

open eq.ops
open list
open list.sorted.ops
open nat
open relation
open sum

namespace list.sorted

section
variables {A : Type} {R : A → A → Prop} [is_transitive R]

definition trans_hd_rel_of_sorted : ∀{x y ys}, R x y → sorted R (y::ys) → hd_rel R x ys
  | x _ []      _     _ := hd_rel.base R x
  | x y (z::zs) x_R_y S := hd_rel.step zs (is_transitive.trans R x_R_y (first_rel S))

variables [is_irreflexive R]

theorem not_mem_of_irrefl_hd_rel : ∀{x ys} (H : hd_rel R x ys) (S : sorted R ys), x ∉ S
  | x []      (hd_rel.base R x)      S := not_mem_nil x
  | x (y::ys) (hd_rel.step ys x_R_y) S :=
    assume x_mem_S : x ∈ S,
    match eq_or_mem_of_mem_cons x_mem_S with
      | or.inl x_eq_y :=
        absurd (x_eq_y⁻¹ ▸ x_R_y) (is_irreflexive.irrefl R x)
      | or.inr x_mem_ys :=
        have not_x_mem_ys : x ∉ ys, from
          not_mem_of_irrefl_hd_rel (trans_hd_rel_of_sorted x_R_y S) (tail S),
        absurd x_mem_ys not_x_mem_ys
    end

theorem not_mem_of_irrefl_hd_tl {x xs} (S : sorted R (x::xs)) : x ∉ xs :=
  have p : hd_rel R x xs ∧ sorted R xs, from sorted_inv S,
  not_mem_of_irrefl_hd_rel (and.left p) (and.right p)

theorem not_mem_of_irrefl {x y ys} (x_R_y : R x y) (S : sorted R (y::ys)) : x ∉ S :=
  not_mem_of_irrefl_hd_rel (hd_rel.step ys x_R_y) S

end

definition fresh : ∀{ns}, sorted gt ns → ℕ
  | []     _ := zero
  | (n::_) _ := succ n

attribute fresh [reducible]

theorem fresh_not_mem (x : ℕ) : ∀{ns} (X : sorted gt ns), x = fresh X → x ∉ X
  | []      _ _          := not_mem_nil x
  | (n::ns) X x_is_fresh := not_mem_of_irrefl (x_is_fresh⁻¹ ▸ lt_succ_self n) X

end list.sorted
