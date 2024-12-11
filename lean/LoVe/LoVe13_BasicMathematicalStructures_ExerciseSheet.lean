/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe Exercise 13: Basic Mathematical Structures

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Type Classes

Recall the inductive type `Tree` we introduced in lecture 5: -/

#check Tree

/- The following function takes two trees and attaches copies of the second
tree to each leaf of the first tree. -/

def Tree.graft {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u =>
    Tree.node a (Tree.graft l u) (Tree.graft r u)

#reduce Tree.graft (Tree.node 1 Tree.nil Tree.nil)
  (Tree.node 2 Tree.nil Tree.nil)

/- 1.1. Prove the following two theorems by structural induction on `t`. -/

theorem Tree.graft_assoc {α : Type} (t u v : Tree α) :
  Tree.graft (Tree.graft t u) v = Tree.graft t (Tree.graft u v) := by
  induction t
  . simp [Tree.graft]
  . simp [Tree.graft]
    apply And.intro
    { exact a_ih }
    { exact a_ih_1 }

theorem Tree.graft_nil {α : Type} (t : Tree α) :
  Tree.graft t Tree.nil = t := by
  induction t
  . simp [graft]
  . simp [graft]
    apply And.intro
    { exact a_ih }
    { exact a_ih_1 }

theorem Tree.nil_graft {α : Type} (t : Tree α) :
  Tree.graft Tree.nil t = t := by
  induction t
  . simp [graft]
  . simp [graft]

/- 1.2. Declare `Tree` an instance of `AddMonoid` using `graft` as the
addition operator. -/

#print AddMonoid

instance Tree.AddMonoid {α : Type} : AddMonoid (Tree α) :=
  { add       := graft
    add_assoc := Tree.graft_assoc
    zero      := Tree.nil
    add_zero  := Tree.graft_nil
    zero_add  := Tree.nil_graft
  }

/- 1.3 (**optional**). Explain why `Tree` with `graft` as addition cannot be
declared an instance of `AddGroup`. -/

#print AddGroup

-- enter your explanation here

/- 1.4 (**optional**). Prove the following theorem illustrating why `Tree`
with `graft` as addition does not constitute an `AddGroup`. -/

theorem Tree.add_left_neg_counterexample :
  ∃x : Tree ℕ, ∀y : Tree ℕ, Tree.graft y x ≠ Tree.nil := by
  apply Exists.intro (Tree.node 0 Tree.nil Tree.nil)
  intro t
  cases t
  . simp [graft]
  . simp [graft]


/- ## Question 2: Multisets and Finsets

Recall the following definitions from the lecture: -/

#check Finset.elems
#check List.elems

/- 2.1. Prove that the finite set of nodes does not change when mirroring a
tree. -/

theorem Finset.elems_mirror (t : Tree ℕ) :
  Finset.elems (mirror t) = Finset.elems t := by
  induction t
  . simp [elems]
  . simp [elems]
    rw [a_ih, a_ih_1]
    ac_rfl

/- 2.2. Show that this does not hold for the list of nodes by providing a
tree `t` for which `List.elems t ≠ List.elems (mirror t)`.

If you define a suitable counterexample, the proof below will succeed. -/

def rottenTree : Tree ℕ :=
  Tree.node 0 (Tree.node 1 Tree.nil Tree.nil) (Tree.node 2 Tree.nil Tree.nil)

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
  ∃t : Tree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe
