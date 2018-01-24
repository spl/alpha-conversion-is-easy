/-

This file contains declarations related to `vrel` inversion or symmetry.

-/

import .id

namespace acie -----------------------------------------------------------------
namespace vrel -----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {R : X ×ν Y} -- Variable name set relations
variables {x : ν∈ X} {y : ν∈ Y} -- Variable name set members

-- `inv R` inverts the order of the relation `R`.
@[reducible]
def inv : X ×ν Y → Y ×ν X :=
  -- An alternative def for this is `function.swap`; however, that does
  -- not unfold as easily as the explicit lambda.
  -- We use type ascription (R : vrel _ _) to improve elaboration/type inference.
  λ R y x, (R : vrel _ _) x y

-- Notation for `inv`.
postfix `°`:std.prec.max_plus := inv

@[reducible]
protected
theorem symm : ⟪x, y⟫ ∈ν R → ⟪y, x⟫ ∈ν R° :=
  λ m, m

end /- namespace -/ vrel -------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
