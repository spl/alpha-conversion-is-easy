import data.list data.set data.list.sorted
open list

namespace set
variables {A : Type} {R : A → A → Prop}

definition of_list : list A → set A
  | []      := empty
  | (x::xs) := insert x (of_list xs)

definition of_sorted {xs} : list.sorted R xs → set A := λS, of_list xs

attribute of_sorted [reducible]

end set
