/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 3 (10 points): Backward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1 (5 points): Connectives and Quantifiers

1.1 (4 points). Complete the following proofs using basic tactics such as
`intro`, `apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem B (a b c : Prop) :
  (a → b) → (c → a) → c → b := by
  intro h₁ h₂ hc
  apply h₁
  apply h₂
  apply hc

theorem S (a b c : Prop) :
  (a → b → c) → (a → b) → a → c := by
  intro h₁ h₂ ha
  apply (h₁ ha (h₂ ha))

theorem more_nonsense (a b c d : Prop) :
  ((a → b) → c → d) → c → b → d := by
  intro h₁ hc hb
  apply (h₁ (fun _ ↦ hb) hc)

theorem even_more_nonsense (a b c : Prop) :
  (a → b) → (a → c) → a → b → c := by
  intro h₁ h₂ ha hb
  apply h₂
  apply ha

/- 1.2 (1 point). Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
  ((((a → b) → a) → a) → b) → b := by
  intro p
  apply p
  intro q
  apply q
  intro a'
  apply p
  intro r
  apply a'


/- ## Question 2 (5 points): Logical Connectives

2.1 (1 point). Prove the following property about double negation using basic
tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `False` at a key point in the
  proof. -/

theorem herman (a : Prop) :
  ¬¬ (¬¬ a → a) := by
  rw [Not]
  intro f
  apply f
  intro nna
  apply False.elim
  apply nna
  intro a'
  apply f
  intro nna'
  apply a'

/- 2.2 (2 points). Prove the missing link in our chain of classical axiom
implications.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw DoubleNegation` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle := by
  rw [ExcludedMiddle]
  intro dn a
  apply dn
  intro h
  apply h
  right
  intro a'
  apply h
  left
  apply a'

/- 2.3 (2 points). We have proved three of the six possible implications
between `ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the
three missing implications, exploiting the three theorems we already have. -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

theorem Peirce_of_DN :
  DoubleNegation → Peirce := by
  intro dn
  apply Peirce_of_EM
  apply EM_of_DN
  apply dn

theorem EM_of_Peirce :
  Peirce → ExcludedMiddle := by
  intro p
  apply EM_of_DN
  apply DN_of_Peirce
  apply p

theorem DN_of_EM :
  ExcludedMiddle → DoubleNegation := by
  intro em
  apply DN_of_Peirce
  apply Peirce_of_EM
  apply em


end BackwardProofs

end LoVe
