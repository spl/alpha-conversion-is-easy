import data.finset

open finset
open nat

inductive exp : finset ℕ → Type :=
  | var : Π {X} x, x ∈ X            → exp X
  | app : Π {X}  , exp X → exp X    → exp X
  | lam : Π {X} x, exp (insert x X) → exp X

open exp

variables {X Y : finset ℕ}

private
definition exp.map_core (e : exp X) : ∀ {Y}, X ⊆ Y → (∀ x, x ∈ X → Σ y, y ∈ Y) → exp Y :=
  begin
    induction e with
      /- var -/ X x x_mem_X
      /- app -/ X e₁ e₂ r₁ r₂
      /- lam -/ X x e r,
    begin /- e: exp.var -/
      intro Y P f,
      obtain y (y_mem_Y : y ∈ Y), from f x x_mem_X,
      var y y_mem_Y
    end,
    begin /- e: exp.app -/
      intro Y P f,
      exact app (r₁ P f) (r₂ P f)
    end,
    begin /- e: exp.lam -/
      intro Y P f,
      have P' : insert x X ⊆ insert x Y, from
        finset.insert_subset_insert x P,
      have f' : Π x', x' ∈ insert x X → Σ y, y ∈ insert x Y, from
        assume x' x'_mem_insert_x_X,
        sigma.mk x' (finset.mem_of_subset_of_mem P' x'_mem_insert_x_X),
      have e' : exp (insert x Y), from r P' f',
      exact lam x e'
    end
  end

definition exp.map (P : X ⊆ Y) (f : ∀ x, x ∈ X → Σ y, y ∈ Y) (e : exp X) : exp Y :=
  @exp.map_core X e Y P f

definition exp.insert (x : ℕ) : exp X → exp (insert x X) :=
  exp.map
    (finset.subset_insert X x)
    (λ x' x'_mem_X, sigma.mk x' (finset.mem_insert_of_mem x x'_mem_X))
