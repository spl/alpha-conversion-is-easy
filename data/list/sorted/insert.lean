import data.list.sorted.basic
import data.list.sorted.mem
import data.sum.trichotomy

open eq.ops
open list
open sigma.ops
open list.sorted.ops
open [class] sum

namespace list.sorted
variables {A : Type}

namespace insert

-- An 'insert.path x xs ys' describes the way 'x' is inserted into the source
-- 'xs' to get the target 'ys'.
inductive path (R : A → A → Prop) (x : A) : list A → list A → Prop :=
  | inserted : ∀{ns},      sorted R (x::ns)                                     → path R x ns      (x::ns)
  | found    : ∀{ns},      sorted R (x::ns)                                     → path R x (x::ns) (x::ns)
  | cons     : ∀{y ms ns}, sorted R (y::ms) → sorted R (y::ns) → path R x ms ns → path R x (y::ms) (y::ns)

end insert

open insert
open insert.path
variable {R : A → A → Prop}

namespace insert

theorem sorted_of_path : ∀{x xs ys}, path R x xs ys → sorted R ys
  | x ns      (x::ns) (inserted S) := S
  | x (x::ns) (x::ns) (found S)    := S
  | x (z::ms) (z::ns) (cons _ S _) := S

lemma swap_tail_with_path_tgt : ∀{x y xs ys}, R x y → path R y xs ys → sorted R (x::xs) → sorted R (x::ys)
  | x y ns      (y::ns) x_R_y (inserted S)  _  := extend x_R_y S
  | x y (y::ns) (y::ns) x_R_y (found _)     S  := S
  | x y (z::ms) (z::ns) _     (cons _ S₁ _) S₂ := extend (first_rel S₂) S₁

lemma mem_path_tgt_of_mem_path_src : ∀{x y} {xs ys}, y ∈ xs → path R x xs ys → y ∈ ys
  | x y ns      (x::ns) y_mem_ns   (inserted _) := mem_cons_of_mem x y_mem_ns
  | x y (x::ns) (x::ns) y_mem_x_ns (found _)    := y_mem_x_ns
  | x y (z::ms) (z::ns) y_mem_z_ms (cons _ _ I) :=
    show y ∈ z::ns, from
    or.elim (iff.elim_left !mem_cons_iff y_mem_z_ms)
      (λy_eq_z : y = z, y_eq_z⁻¹ ▸ mem_cons z ns)
      (λy_mem_ms : y ∈ ms, mem_cons_of_mem _ (mem_path_tgt_of_mem_path_src y_mem_ms I))

lemma mem_path_tgt : ∀{x xs ys}, path R x xs ys → x ∈ ys
  | x ns      (x::ns) (inserted _) := mem_cons x ns
  | x (x::ns) (x::ns) (found _)    := mem_cons x ns
  | x (y::ms) (y::ns) (cons _ _ I) :=
    iff.elim_right !mem_cons_iff (or.inr (mem_path_tgt I))

end insert

open insert
variable [sum.is_trichotomic R]

definition insert : ∀x {xs}, sorted R xs → sigma (path R x xs)
  | x []      _ := sigma.mk [x] (inserted (sorted_singleton x))
  | x (y::ys) S :=
    sum.trichotomy.by_cases
      (assume x_R_y : R x y,
        sigma.mk (x::y::ys) (inserted (extend x_R_y S)))
      (assume x_eq_y : x = y,
        sigma.mk (y::ys) (x_eq_y⁻¹ ▸ found S))
      (assume y_R_x : R y x,
        obtain ys' (I : path R x ys ys'), from insert x (tail S),
        sigma.mk (y::ys') (cons S (swap_tail_with_path_tgt y_R_x I S) I))

definition sorted_insert x {xs} (S : sorted R xs) : sigma (sorted R) :=
  sigma.imp_sigma (λys, sorted_of_path) (insert x S)

theorem mem_insert x {xs} (S : sorted R xs) : x ∈ (insert x S).1 :=
  mem_path_tgt (insert x S).2

end list.sorted
