/-

This file contains the proof that `aexp` is a `category`.

-/

import .properties
import data.category

namespace acie -----------------------------------------------------------------
namespace aexp -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets

instance category : category aexp.subst :=
  { comp     := @has_comp.comp (vs V) _ _
  , id       := aexp.subst.id
  , left_id  := λ X Y, aexp.subst.left_id
  , right_id := λ X Y, aexp.subst.right_id
  , assoc    := λ W X Y Z, aexp.subst.assoc
  }

end /- namespace -/ aexp -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
