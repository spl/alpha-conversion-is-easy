import data.set

--------------------------------------------------------------------------------

open eq.ops
open prod.ops
open set

--------------------------------------------------------------------------------

definition symm_update₁ (R : set (ℕ × ℕ)) (x y : ℕ) : set (ℕ × ℕ) :=
  λ p, p = (x, y) ∨ p.1 ≠ x ∧ p.1 ≠ y ∧ p ∈ R

--------------------------------------------------------------------------------

variables {A : Type} {X Y Z : set A}

definition sset (X : set A) (Y : set A) : Type :=
  A → A → Prop

--------------------------------------------------------------------------------

namespace sset

definition mem (x y : A) (S : sset X Y) :=
  x ∈ X ∧ y ∈ Y ∧ S x y

theorem mem_left {x y : A} {S : sset X Y} (H : mem x y S) : x ∈ X :=
  and.left H

theorem mem_right {x y : A} {S : sset X Y} (H : mem x y S) : y ∈ Y :=
  and.left (and.right H)

theorem mem_prop {x y : A} {S : sset X Y} (H : mem x y S) : S x y :=
  and.right (and.right H)

definition to_set (S : sset X Y) : set (A × A) :=
  λ p, mem p.1 p.2 S

definition from_set (X : set A) (Y : set A) (S : set (A × A)) : sset X Y :=
  λ m n, m ∈ X ∧ n ∈ Y ∧ (m, n) ∈ S

definition insert (x y : A) (S : sset X Y) : sset (set.insert x X) (set.insert y Y) :=
  λ m n, m = x ∧ n = y ∨ mem m n S

definition id (X : set A) : sset X X :=
  λ m n, m = n ∧ m ∈ X

definition converse (R : sset X Y) : sset Y X :=
  λ m n, mem n m R

definition compose (R : sset X Y) (S : sset Y Z) : sset X Z :=
  λ m n, ∃ y, mem m y R ∧ mem y n S

section mem_compose
variables {x z : A} {R : sset X Y} {S : sset Y Z}

private
lemma mem_compose.left (H : (∃ y, mem x y R ∧ mem y z S)) : mem x z (compose R S) :=
  obtain (y : A) (Hy : mem x y R ∧ mem y z S), from H,
  have x_y_mem_R : mem x y R, from and.left Hy,
  have y_z_mem_S : mem y z S, from and.right Hy,
  have x_mem_X : x ∈ X, from mem_left x_y_mem_R,
  have z_mem_Z : z ∈ Z, from mem_right y_z_mem_S,
  have R_compose_S_applied : compose R S x z, from
    exists.intro y (and.intro x_y_mem_R y_z_mem_S),
  show mem x z (compose R S), from
    and.intro x_mem_X (and.intro z_mem_Z R_compose_S_applied)

private
lemma mem_compose.right (H : mem x z (compose R S)) : ∃ y, mem x y R ∧ mem y z S :=
  and.right (and.right H)

theorem mem_compose : (∃ y, mem x y R ∧ mem y z S) ↔ mem x z (compose R S) :=
  iff.intro mem_compose.left mem_compose.right

end mem_compose

end sset

--------------------------------------------------------------------------------

open sset

definition symm_update (R : sset X Y) (x y : A) : sset (insert x X) (insert y Y) :=
  λ m n, m = x ∧ n = y ∨ m ≠ x ∧ n ≠ y ∧ mem m n R

--------------------------------------------------------------------------------

section symm_update_and_id
variables {x a b : A}

private
lemma mem_symm_update_id.left
(H : mem a b (symm_update (id X) x x))
: mem a b (id (insert x X)) :=
  have a_mem_insert_x_X : a ∈ insert x X, from and.left H,
  have b_mem_insert_x_X : b ∈ insert x X, from and.left (and.right H),
  have H' : a = x ∧ b = x ∨ a ≠ x ∧ b ≠ x ∧ mem a b (id X), from
    and.right (and.right H),
  have a_eq_b : a = b, from
    or.elim H'
      (suppose H₁ : a = x ∧ b = x,
       have a_eq_x : a = x, from and.left H₁,
       have b_eq_x : b = x, from and.right H₁,
       b_eq_x⁻¹ ▸ a_eq_x)
      (suppose H₁ : a ≠ x ∧ b ≠ x ∧ mem a b (id X),
       have a_eq_b : a = b, from
         and.left (and.right (and.right (and.right (and.right H₁)))),
       a_eq_b),
  show mem a b (id (insert x X)), from
    and.intro a_mem_insert_x_X
    (and.intro b_mem_insert_x_X
    (and.intro a_eq_b a_mem_insert_x_X))

variable [decidable_eq A]

private
lemma mem_symm_update_id.right
(H : mem a b (id (insert x X)))
: mem a b (symm_update (id X) x x) :=
  have a_mem_insert_x_X : a ∈ insert x X, from and.left H,
  have b_mem_insert_x_X : b ∈ insert x X, from and.left (and.right H),
  have a_eq_b : a = b, from and.left (and.right (and.right H)),
  have symm_update_id : symm_update (id X) x x a b, from
    if P : a = x then
      have a_eq_x : a = x, from P,
      have b_eq_x : b = x, from a_eq_b ▸ a_eq_x,
      or.inl (and.intro a_eq_x b_eq_x)
    else
      have a_ne_x : a ≠ x, from P,
      have b_ne_x : b ≠ x, from a_eq_b ▸ a_ne_x,
      have a_mem_X : a ∈ X, from
        mem_of_mem_insert_of_ne a_mem_insert_x_X a_ne_x,
      have b_mem_X : b ∈ X, from
        mem_of_mem_insert_of_ne b_mem_insert_x_X b_ne_x,
      have a_b_mem_id_X : mem a b (id X), from
        and.intro a_mem_X
        (and.intro b_mem_X
        (and.intro a_eq_b a_mem_X)),
      or.inr (and.intro a_ne_x (and.intro b_ne_x a_b_mem_id_X)),
  show mem a b (symm_update (id X) x x), from
    and.intro a_mem_insert_x_X (and.intro b_mem_insert_x_X symm_update_id)

theorem mem_symm_update_id
: mem a b (symm_update (id X) x x)
↔ mem a b (id (insert x X)) :=
  iff.intro mem_symm_update_id.left mem_symm_update_id.right

end symm_update_and_id

--------------------------------------------------------------------------------

section symm_update_and_compose
variables {R : sset X Y} {S : sset Y Z} {x y z a c : A}

theorem mem_symm_update_compose_of_mem_compose_symm_update
(H : mem a c (compose (symm_update R x y) (symm_update S y z)))
: mem a c (symm_update (compose R S) x z) :=
  have a_mem_insert_x_X : a ∈ insert x X, from and.left H,
  have c_mem_insert_z_Z : c ∈ insert z Z, from and.left (and.right H),
  obtain (b : A) (Hb : mem a b (symm_update R x y) ∧ mem b c (symm_update S y z)), from
    and.right (and.right H),
  have symm_update_R_x_y : symm_update R x y a b, from
    and.right (and.right (and.left Hb)),
  have symm_update_S_y_z : symm_update S y z b c, from
    and.right (and.right (and.right Hb)),
  have inl_symm_update : a = x ∧ b = y → symm_update (compose R S) x z a c, from
    suppose H₁ : a = x ∧ b = y,
    have a_eq_x : a = x, from and.left H₁,
    have b_eq_y : b = y, from and.right H₁,
    or.elim symm_update_S_y_z
      (suppose H₂ : b = y ∧ c = z,
       have c_eq_z : c = z, from and.right H₂,
       or.inl (and.intro a_eq_x c_eq_z))
      (suppose H₂ : b ≠ y ∧ c ≠ z ∧ mem b c S,
       have b_ne_y : b ≠ y, from and.left H₂,
       absurd b_eq_y b_ne_y),
  have inr_symm_update : a ≠ x ∧ b ≠ y ∧ mem a b R → symm_update (compose R S) x z a c, from
    suppose H₁ : a ≠ x ∧ b ≠ y ∧ mem a b R,
    have a_ne_x : a ≠ x, from and.left H₁,
    have b_ne_y : b ≠ y, from and.left (and.right H₁),
    have a_b_mem_R : mem a b R, from and.right (and.right H₁),
    or.elim symm_update_S_y_z
      (suppose H₂ : b = y ∧ c = z,
       have b_eq_y : b = y, from and.left H₂,
       absurd b_eq_y b_ne_y)
      (suppose H₂ : b ≠ y ∧ c ≠ z ∧ mem b c S,
       have c_ne_z : c ≠ z, from and.left (and.right H₂),
       have b_c_mem_S : mem b c S, from and.right (and.right H₂),
       have a_c_mem_compose_R_S : mem a c (compose R S), from
         iff.elim_left mem_compose (exists.intro b (and.intro a_b_mem_R b_c_mem_S)),
       or.inr (and.intro a_ne_x (and.intro c_ne_z a_c_mem_compose_R_S))),
  have symm_update_compose : symm_update (compose R S) x z a c, from
    or.elim symm_update_R_x_y inl_symm_update inr_symm_update,
  show mem a c (symm_update (compose R S) x z), from
    and.intro a_mem_insert_x_X (and.intro c_mem_insert_z_Z symm_update_compose)

end symm_update_and_compose
