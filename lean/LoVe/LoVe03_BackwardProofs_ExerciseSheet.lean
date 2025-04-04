/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
  a → a :=
  by
    intro ha
    apply ha

theorem K (a b : Prop) :
  a → b → b :=
    by
      intro a b
      apply b

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
    by
      intro f
      intro b a
      apply f
      apply a
      apply b

theorem proj_fst (a : Prop) :
  a → a → a :=
  by
    intro a
    intro ha
    apply ha


/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  by
    intro a aa
    apply aa

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  by
    intro f a
    intro g b
    apply f
    apply a
    apply b

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  by
    intro f not_b a
    apply not_b
    apply f
    apply a



/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    {
      intro h
      apply And.intro
      {
        intro x
        exact And.left (h x)
      }
      {
        intro x
        exact And.right (h x)
      }
    }
    {
      intro f
      intro x
      apply And.intro
      exact And.left f x
      exact And.right f x
    }


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul 9 1

theorem mul_zero (n : ℕ) :
  mul 0 n = 0 :=
  by
    induction n with
      | zero => rfl
      | succ n' ih =>
        rw [mul]
        rw [ih]
        rw [add]


#check add_succ
theorem mul_succ (m n : ℕ) :
  mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
      | zero =>
        rfl
      | succ n' ih =>
        rw [mul]
        rw [add]
        rw [add_succ]
        rw [mul]
        rw [ih]
        ac_rfl


/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  by
    induction n with
    | zero =>
      rw [mul]
      rw [mul_zero]
    | succ n' ih =>
      rw [mul]
      rw [mul_succ]
      rw [ih]
      rw [add_comm]


theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  by
    induction l with
      | zero =>
        rw  [mul_zero]
        rw [mul_zero]
        rw [mul_zero]
      | succ n' ih =>
        rw [mul_comm]
        rw [mul_succ]
        rw [mul_succ]
        rw [mul_add]
        rw [mul_comm]
        rw [ih]
        simp [mul_comm]






/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
  by
    induction n with
      | zero =>
        rw [mul_comm]
        rw [mul_zero]
        rw [mul_zero]
        rw [add_zero]
        rw [mul_zero]
      | succ n' ih =>
        rw [mul_comm]
        rw [mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
  by
    rw [ExcludedMiddle]
    intro ex a b p
    apply Or.elim
    {
      apply ex
    }
    {
      intro ha
      exact ha
    }
    {
      intro not_a
      apply p
      intro ha
      apply False.elim
      apply not_a
      apply ha
    }

/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
    by
      rw [Peirce, DoubleNegation]
      intro p a nna
      apply p a False
      intro haf
      apply False.elim
      apply nna
      intro ha
      exact haf ha



/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
    by
      rw [DoubleNegation, ExcludedMiddle]
      intro d b
      apply d
      intro ha
      apply ha
      apply Or.inr
      intro hb
      apply ha
      apply Or.inl
      exact hb

end SorryTheorems

end BackwardProofs

end LoVe
