/-

This file is a port of part of data.list.set from the Lean 2 standard library
to Lean 3.

-/

namespace list

variables {A : Type} [decidable_eq A]

theorem insert_eq_of_mem {a : A} {l : list A} : a ∈ l → insert a l = l :=
λ c, if_pos c

theorem insert_eq_of_not_mem {a : A} {l : list A} : a ∉ l → insert a l = a::l :=
λ c, if_neg c

end list
