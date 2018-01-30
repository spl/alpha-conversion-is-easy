import aeq
import data.finset.vset

namespace acie ------------------------------------------------------------------

open exp

def X : finset ℕ := {1}
def Y : finset ℕ := {2}
def Z : finset ℕ := {3}

@[simp]
def var' (n : ℕ) : exp {n} :=
  var ⟨n, finset.mem_insert_self n ∅⟩

def sub (m n : ℕ) : subst {m} {n} :=
  λ (x : ν∈ {m}),
  if h : x.1 = m then
    var' n
  else
    have p : x.1 ∈ finset.erase (insert m ∅) m := finset.mem_erase.mpr ⟨h, x.2⟩,
    have q : x.1 ∉ ∅ := finset.not_mem_empty x.1,
    absurd (by rw finset.erase_insert (finset.not_mem_empty m) at p; exact p) q

def F : subst X Y := sub 1 2
def G : subst Y Z := sub 2 3

example : subst.apply F (var' 1) = var' 2 := rfl
example : subst.apply G (var' 2) = var' 3 := rfl
example : subst.apply G (subst.apply F (var' 1)) = var' 3 := rfl
example : subst.apply G (subst.apply F (var' 1)) = subst.apply (subst.apply G ∘ F) (var' 1) := rfl

def v1 : exp X := lam' 2 (insert_var 2 (var' 1))
example : subst.apply F v1 = lam' 3 (insert_var 3 (var' 2)) := rfl
example : subst.apply G (subst.apply F v1) = lam' 4 (insert_var 4 (var' 3)) := rfl
example : subst.apply G (subst.apply F v1) = subst.apply (subst.apply G ∘ F) v1 := by refl
example : subst.apply (subst.update (fresh X).1 (fresh Y).1 F) (insert_var (fresh X).1 v1) = lam' 4 (var ⟨2, _⟩) := rfl
example : insert_var (fresh Y).1 (subst.apply F v1) = lam' 3 (var ⟨2, _⟩) := rfl
example : subst.apply (subst.update (fresh X).1 (fresh Y).1 F) (insert_var (fresh X).1 v1) ≡α⟨vrel.id (insert (fresh Y).1 Y)⟩ insert_var (fresh Y).1 (subst.apply F v1) :=
  begin
    simp [v1],
    rw [insert_var.lam_comp (insert_var 2 (var ⟨1, _⟩)), subst.apply, subst.apply],
    rw insert_var.lam_self (subst.apply (subst.update 2 ((fresh Y).fst) F) (insert_var 2 (var ⟨1, _⟩))),
    apply aeq.lam,
    rw [insert_var.var, insert_var.var, map, subst.apply, subst.apply, vname.insert, vname.insert, vname.map_of_subset],
    simp [subst.update],
    have one_ne_two : 1 ≠ 2 := dec_trivial,
    rw dif_neg one_ne_two,
    have p : (fresh X).1 = 2 := rfl, rw p, clear p,
    rw dif_neg one_ne_two,
    have p : (fresh Y).1 = 3 := rfl, rw p, clear p,
    have p : (fresh (insert 3 Y)).1 = 4 := rfl, rw p, clear p,
    simp [vname.erase],
    have p : F ⟨1, _⟩ = var ⟨2, _⟩ := rfl, rw p, clear p,
    simp [insert_var.var],
    apply aeq.var,
    simp [vrel.update],
    right,
    rw [vname.insert, vname.insert, vname.insert],
    have two_ne_four : 2 ≠ 4 := dec_trivial,
    existsi two_ne_four,
    have two_ne_three : 2 ≠ 3 := dec_trivial,
    existsi two_ne_three,
    simp [vname.erase, vrel.id]
  end

def v2 : exp X := insert_var 1 (lam' 1 (var' 1))
example : subst.apply F v2 = lam' 3 (var (vname.insert_self 3 Y)) := rfl
example : subst.apply G (subst.apply F v2) = lam' 4 (var (vname.insert_self 4 Z)) := rfl
example : subst.apply (subst.apply G ∘ F) v2 = lam' 4 (var (vname.insert_self 4 Z)) := rfl
example : subst.apply G (subst.apply F v2) = subst.apply (subst.apply G ∘ F) v2 := by refl
example : subst.apply (subst.update (fresh X).1 (fresh Y).1 F) (insert_var (fresh X).1 v2) = lam' 4 (var (vname.insert_self 4 (insert (fresh Y).1 Y))) := rfl
example : insert_var (fresh Y).1 (subst.apply F v2) = lam' 3 (var (vname.insert_self 3 (insert (fresh Y).1 Y))) := rfl

end /- namespace -/ acie -------------------------------------------------------
