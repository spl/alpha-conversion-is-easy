import data.list.sorted
open list

namespace list.sorted
variables {A : Type} {R : A → A → Prop} {x x₁ x₂ : A} {xs : list A}

definition extend : R x₁ x₂ → sorted R (x₂::xs) → sorted R (x₁::x₂::xs) :=
  λ p, sorted.step (hd_rel.step xs p)

definition tail : ∀{x xs}, sorted R (x::xs) → sorted R xs
  | _ []     _            := sorted.base R
  | _ (_::_) (extend p S) := S

definition first_rel : sorted R (x₁::x₂::xs) → R x₁ x₂ :=
  λ S, hd_rel_inv (and.left (sorted_inv S))

end list.sorted
