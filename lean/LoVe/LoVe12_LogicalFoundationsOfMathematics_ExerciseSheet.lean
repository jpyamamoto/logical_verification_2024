/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe Exercise 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Vectors as Subtypes

Recall the definition of vectors from the demo: -/

#check Vector

/- The following function adds two lists of integers elementwise. If one
function is longer than the other, the tail of the longer list is ignored. -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. Show that if the lists have the same length, the resulting list also
has that length. -/

theorem List.length_add :
  ∀xs ys, List.length xs = List.length ys →
    List.length (List.add xs ys) = List.length xs
  | [], [] => fun _ ↦ rfl
  | x :: xs, y :: ys => by
    simp [add, List.length]
    intro h
    apply List.length_add xs ys h
  | [], y :: ys => by
    simp [add]
  | x :: xs, [] => by
    simp [add]

/- 1.2. Define componentwise addition on vectors using `List.add` and
`List.length_add`. -/

def Vector.add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n
  | u, v => Subtype.mk (List.add (Subtype.val u) (Subtype.val v)) (
    by
      rw [List.length_add]
      . exact Subtype.property u
      . rw [Subtype.property u, Subtype.property v]
  )

/- 1.3. Show that `List.add` and `Vector.add` are commutative. -/

theorem List.add.comm :
  ∀xs ys, List.add xs ys = List.add ys xs
  | [], [] => rfl
  | x :: xs, y :: ys => by
    simp [add]
    apply And.intro
    . simp [Int.add_comm]
    . exact List.add.comm xs ys
  | x :: xs, [] => by simp [add]
  | [], y :: ys => by simp [add]

theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
  Vector.add u v = Vector.add v u := by
  apply Subtype.eq
  simp [Vector.add]
  exact List.add.comm _ _

/- ## Question 2: Integers as Quotients

Recall the construction of integers from the lecture, not to be confused with
Lean's predefined type `Int` (= `ℤ`): -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. Define negation on these integers. Observe that if `(p, n)` represents
an integer, then `(n, p)` represents its negation. -/

def Int.neg : Int → Int :=
  Quotient.lift (fun pn : ℕ × ℕ ↦ ⟦(Prod.snd pn, Prod.fst pn)⟧) (
  by
    intro a b hr
    cases a
    cases b
    apply Quotient.sound
    simp [Int.Setoid_Iff] at *
    linarith
  )

/- 2.2. Prove the following theorems about negation. -/

theorem Int.neg_eq (p n : ℕ) :
  Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ := by rfl

theorem int.neg_neg (a : Int) :
  Int.neg (Int.neg a) = a := by
  induction a using Quotient.inductionOn
  . cases a_1
    simp [Int.neg]

end LoVe
