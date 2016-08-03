import data.list.sorted.insert

open eq.ops
open list
open sigma.ops
open [class] sum

namespace list.sorted
variables {A : Type}

namespace union

-- An 'union.path x xs ys' describes the way left source 'xs' is unioned with
-- the right source 'ys' to get the target 'zs'.
inductive path (R : A → A → Prop) : list A → list A → list A → Type :=
  | nil  : Π {ys},            sorted R ys                             → path R []      ys ys
  | cons : Π {x xs ys ms zs}, insert.path R x ms zs → path R xs ys ms → path R (x::xs) ys zs

end union

open union
open union.path
variable {R : A → A → Prop}

namespace union

definition sorted_of_path : ∀{xs ys zs}, path R xs ys zs → sorted R zs
  | []     _ _ (nil S)    := S
  | (_::_) _ _ (cons I _) := insert.sorted_of_path I

end union

open union
variable [sum.is_trichotomic R]

definition list_union : ∀xs {ys}, list.sorted R ys → sigma (path R xs ys)
  | []      ys S := sigma.mk ys (nil S)
  | (x::xs) ys S :=
    obtain ms U, from list_union xs S,
    obtain ns I, from insert x (sorted_of_path U),
    sigma.mk ns (cons I U)

definition union {xs ys} (S : sorted R xs) : sorted R ys → sigma (path R xs ys) :=
  list_union xs

namespace union

lemma mem_path_left : ∀{x xs ys zs}, x ∈ xs → path R xs ys zs → x ∈ zs
  | x []       ys ys x_mem_xs (nil _)    := absurd x_mem_xs (not_mem_nil x)
  | x (x'::xs) ys zs x_mem_xs (cons I U) :=
    or.elim (iff.elim_left (mem_cons_iff x x' xs) x_mem_xs)
      (λ x_eq_x, x_eq_x⁻¹ ▸ insert.mem_path_tgt I)
      (λ x_mem_xs, insert.mem_path_tgt_of_mem_path_src (mem_path_left x_mem_xs U) I)

lemma mem_path_right : ∀{y xs ys zs}, y ∈ ys → path R xs ys zs → y ∈ zs
  | y []     ys ys y_mem_ys (nil _)    := y_mem_ys
  | y (_::_) ys zs y_mem_ys (cons I U) :=
    insert.mem_path_tgt_of_mem_path_src (mem_path_right y_mem_ys U) I

end union

namespace ops
notation a ∪ b := union a b
end ops

open ops
open union
variables (x y : A) {xs ys : list A} {S₁ : sorted R xs} {S₂ : sorted R ys}

theorem mem_union_left : x ∈ S₁ → x ∈ (S₁ ∪ S₂).1 :=
  λ x_mem_S₁, mem_path_left x_mem_S₁ (S₁ ∪ S₂).2

theorem mem_union_right : y ∈ S₂ → y ∈ (S₁ ∪ S₂).1 :=
  λ y_mem_S₂, mem_path_right y_mem_S₂ (S₁ ∪ S₂).2

end list.sorted
