/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4 (10 points): Forward Proofs

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha

    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1 (2 points). Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem about_Impl_term :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
fun a b h1 h2=>
  Or.elim h1
    (fun na => False.elim (na h2))
    (fun b => b)






/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume h : ¬ a ∨ b

  show a → b from
    Or.elim h
      (
        assume na : ¬a
        assume aa : a
        have f :=
          na aa
        show b from
         False.elim
         f
      )
      (
        assume hb : b
        assume ha : a
        show b from
          hb
      )


/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
    Iff.intro
  (
    -- Assume our hypothesis
    assume h : ∀x, p x ∨ q x
    assume x : α
    have hx :=
      h x
    Or.elim hx
    (
      assume px : p x
      show q x ∨ p x from
        Or.inr px
    )
    (
      assume qx : q x
      show q x ∨ p x from
        Or.inl qx
    )
  )
  (
    assume h : ∀x, q x ∨ p x
    assume x : α
    have hx : q x ∨ p x := h x
    Or.elim hx
      (
        assume qx : q x
        show p x ∨ q x from
          Or.inr qx
      )
      (
        assume px : p x
        show p x ∨ q x from
          Or.inl px
      )
  )

/- 2.2 (3 points). We have proved or stated three of the six possible
implications between `ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the
exercise of lecture 3. Prove the three missing implications using structured
proofs, exploiting the three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
  DoubleNegation → Peirce :=
  assume dn : DoubleNegation
  have em : ExcludedMiddle := SorryTheorems.EM_of_DN dn
  have pierce : Peirce := Peirce_of_EM em
  peirce

-- Want to see if I can prove DoubleNegation implies Peirce without the help of some of the
-- theorems
theorem Peirce_of_DN_full :
  DoubleNegation → Peirce :=
    assume dn : DoubleNegation
    fix a b : Prop
    sorry



theorem EM_of_Peirce :
  Peirce → ExcludedMiddle :=
  assume p : Peirce
  have pofd : DoubleNegation := DN_of_Peirce p
  SorryTheorems.EM_of_DN pofd


theorem dn_of_em :
  ExcludedMiddle → DoubleNegation :=
  assume ex : ExcludedMiddle


end BackwardProofs

end LoVe
