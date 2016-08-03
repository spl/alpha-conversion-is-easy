namespace relation

structure is_irreflexive [class] {A : Type} (R : A → A → Prop) :=
  (irrefl : irreflexive R)

end relation
