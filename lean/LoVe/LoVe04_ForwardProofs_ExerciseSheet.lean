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
  show a from
    ha

theorem K (a b : Prop) :
  a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  assume f : (a → b → c)
  assume hb : b
  assume ha : a
  have hc : c :=
    f ha hb
  show c from
    hc


theorem proj_fst (a : Prop) :
  a → a → a :=
  assume ha : a
  assume haa : a
  show a from
    haa

/- Please give a different answer than for `proj_fst`. -/
/- Hmm will have to come back to this one later-/
theorem proj_snd (a : Prop) :
  a → a → a :=
  sorry


theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  assume f : (a → b → c)
  assume ha : a
  assume g : (a → c)
  assume hb : b
  show c from
    g ha

/- 1.2. Supply a structured proof of the contraposition rule. -/
theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  assume f : (a → b)
  assume not_b : ¬ b
  assume ha : a
  have hb : b :=
    f ha
  show False from
    not_b hb

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/
theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
    Iff.intro
      (assume pax : ∀x, p x ∧ q x
        show (∀x, p x) ∧ (∀x, q x)
          by
          simp [pax])
      (assume pandx : (∀x, p x) ∧ (∀x, q x)
        show (∀x, p x ∧ q x) by
          simp [pandx])


-- For some reason simp works so trying to do this proof a little more explicitly
theorem forall_and_two {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
    Iff.intro
      (assume pax : ∀x, p x ∧ q x
        show (∀x, p x) ∧ (∀x, q x) from
          assume x : α
          have px : Prop :=
            p x
          have q x : Prop :=
           q x
          show (∀x, p x) ∧ (∀x, q x) from
            by
              exact [px, qx]
              rfl)
      (assume pandx : (∀x, p x) ∧ (∀x, q x)
        show (∀x, p x ∧ q x) by
        apply pandx
          )

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume f : (∃x, ∀y, p x y)
  assume y : α
  show (∃x, p x y) from
    Exists.elim f (
      fix x : α
      assume h : ∀y, p x y
      show ∃ x, p x y from
        Exists.intro x (h y)
    )


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

theorem binomial_square (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
    by
      simp [mul_add]
      simp [add_mul]
      simp [Nat.two_mul]
      simp [mul_comm]
      simp [mul_add]
      simp [mul_comm]
      simp [add_assoc]


/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  assume f : (a + b) * (a + b)
  assume g : a * a + 2 * a * b + b * b
  have sf :=
    mul_add f
  have ssf :=
    add_mul sf
  have sg :=
    Nat.two_mul g
  have ssg :=
    mul_add sg
  have sssg :=
    mul_comm ssg
  have abb :=
    add_assoc f
  show f = g by
    rfl


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
  False :=
  sorry

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  sorry

end LoVe
