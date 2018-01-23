/-

This files defines the `subst.update` definition and theorems.

-/

import .type
import exp.map

namespace acie -----------------------------------------------------------------
namespace exp ------------------------------------------------------------------
namespace subst ----------------------------------------------------------------

variables {V : Type} [decidable_eq V] -- Type of variable names
variables {a b : V} -- Variable names
variables {vs : Type → Type} [vset vs V] -- Type of variable name sets
variables {X Y : vs V} -- Variable name sets
variables {F : subst X Y} -- Substitutions

-- Update a given substitution with a new variable substitution
@[reducible]
protected
def update (a b : V) (F : subst X Y) : subst (insert a X) (insert b Y) :=
  λ (x : ν∈ insert a X),
  if p : x.1 = a then
    var (vname.insert_self b Y)
  else
    insert_var b (F (vname.erase x p))

namespace update ---------------------------------------------------------------

protected
theorem eq (x : ν∈ insert a X) (p : x.1 = a)
: subst.update a b F x = var (vname.insert_self b Y) :=
  by simp [subst.update, dif_pos p]

protected
theorem eq_self
: subst.update a b F (vname.insert_self a X) = var (vname.insert_self b Y) :=
  update.eq (vname.insert_self a X) rfl

protected
theorem ne (F : subst X Y) (x : ν∈ insert a X) (p : x.1 ≠ a)
: subst.update a b F x = insert_var b (F (vname.erase x p)) :=
  by simp [subst.update, dif_neg p]

protected
theorem lift (a b : V) (F : X →ν Y)
: subst.update a b (subst.lift F) = subst.lift (vname.update a b F) :=
  begin
    funext x,
    cases x with c pc,
    simp [subst.update, subst.lift, function.comp, vname.update],
    cases decidable.em (c = a) with c_eq_a c_ne_a,
    begin /- c_eq_a : c = a -/
      simp [dif_pos c_eq_a]
    end,
    begin /- c_ne_a : c ≠ a -/
      simp [dif_neg c_ne_a, insert_var, map, vname.insert],
      reflexivity
    end
  end

end /- namespace -/ update -----------------------------------------------------

end /- namespace -/ subst ------------------------------------------------------
end /- namespace -/ exp --------------------------------------------------------
end /- namespace -/ acie -------------------------------------------------------
