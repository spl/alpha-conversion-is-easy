import data.list
import data.list.sorted
open list

namespace list.sorted
variables {A : Type} {R : A → A → Prop} {x : A} {xs : list A}

definition mem (x : A) : sorted R xs → Prop :=
  λ S, x ∈ xs

attribute mem [reducible]

definition decidable_mem [instance] [decidable_eq A] (x : A) (S : sorted R xs) : decidable (mem x S) :=
  list.decidable_mem x xs

namespace ops
notation x ∈ S := mem x S
notation x ∉ S := ¬ x ∈ S
end ops

end list.sorted
