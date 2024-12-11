/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
  a → a :=
  assume ha : a
  show a from ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from habc ha hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha₁ : a
  assume ha₂ : a
  show a from ha₁

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  assume ha₁ : a
  assume ha₂ : a
  show a from ha₂

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from hac ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : ¬ b
  assume ha : a
  show False from
    hnb (hab ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume hfa : ∀x, p x ∧ q x
    have hpx : ∀x, p x :=
      fix x : α
      show p x from And.left (hfa x)
    have hqx : ∀x, q x :=
      fix x : α
      show q x from And.right (hfa x)
    show (∀x, p x) ∧ (∀x, q x) from And.intro hpx hqx)
    (assume hlr : (∀x, p x) ∧ (∀x, q x)
    fix x : α
    have hpx := hlr.left x
    have hqx := hlr.right x
    show p x ∧ q x from
      And.intro hpx hqx)

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hef : ∃x, ∀y, p x y
  fix y : α
  Exists.elim hef 
    (fix x : α
     assume hpxy : ∀y, p x y
     Exists.intro x (hpxy y))

/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

#check mul_add
#check add_mul
#check add_comm
#check add_assoc
#check mul_comm
#check mul_assoc
#check Nat.two_mul

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := by rw [add_mul]
    _ = a * a + a * b + b * a + b * b := by simp [mul_add, add_assoc]
    _ = a * a + a * b + a * b + b * b := by simp [mul_comm]
    _ = a * a + (a * b + a * b) + b * b := by simp [add_assoc]
    _ = a * a + (2 * (a * b)) + b * b := by rw [← Nat.two_mul]
    _ = a * a + 2 * a * b + b * b := by simp [add_assoc, mul_assoc]

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  sorry


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  have h : (∀x : Prop, x = False ∧ True) ↔ True := 
    (All.one_point_wrong False (fun _ ↦ True))
  have h'' : ∀x : Prop, x = False ∧ True := Iff.mpr h True.intro
  have h''' : True = False := (h'' True).left
  show False from Eq.mp h''' True.intro


/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

#check Exists.elim
#check Exists.intro

theorem Exists.proof_of_False :
  False :=
  have h : (∃x : Prop, x = True → False) ↔ False := 
    (Exists.one_point_wrong True (fun _ ↦ False))
  show False from Iff.mp h (Exists.intro (¬ True) (
    assume h'' : (¬ True) = True
    show False from
      by
        simp at h''
    ))

end LoVe
