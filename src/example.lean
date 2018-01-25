import aeq
import data.finset.vset

namespace acie ------------------------------------------------------------------

open exp

def X : finset ℕ := {1}
def Y : finset ℕ := {2}
def Z : finset ℕ := {3}

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

def v1 : exp X := lam' 2 (insert_var 2 (var' 1))
example : subst.apply F v1 = lam' 3 (insert_var 3 (var' 2)) := rfl
example : subst.apply G (subst.apply F v1) = lam' 4 (insert_var 4 (var' 3)) := rfl

def v2 : exp ∅ := lam' 1 (var' 1)
example : insert_var 1 v2 = lam' 1 (insert_var 1 (var' 1)) := rfl
example : subst.apply F (insert_var 1 v2) = lam' 3 (var (vname.insert_self 3 Y)) := rfl
example : subst.apply G (subst.apply F (insert_var 1 v2)) = lam' 4 (var (vname.insert_self 4 Z)) := rfl

end /- namespace -/ acie -------------------------------------------------------
