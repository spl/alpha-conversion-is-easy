namespace sum

universe variables u v

variable {A : Type.{u}}
variable R : A → A → Type.{v}

theorem trichotomy : Type.{max 1 u v} := ∀(a b : A), sum (R a b) (sum (a = b) (R b a))

structure is_trichotomic [class] (R : A → A → Type.{v}) := (trich : trichotomy R)

variables {R} [is_trichotomic R] {a b : A} {P : Type}

reveal trichotomy

theorem trichotomy.by_cases (H₁ : R a b → P) (H₂ : a = b → P) (H₃ : R b a → P) : P :=
  match is_trichotomic.trich R a b with
    | sum.inl a_R_b            := H₁ a_R_b
    | sum.inr (sum.inl a_eq_b) := H₂ a_eq_b
    | sum.inr (sum.inr b_R_a)  := H₃ b_R_a
  end

end sum
