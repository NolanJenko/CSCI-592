/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
  Odd 1 := by
  intro h
  cases h


/- 1.2. Prove that 3 and 5 are odd. -/

-- enter your answer here

@[simp] theorem Odd_3 :
  Odd 3 :=
    by
      intro h
      cases h with
        | add_two t ht =>
          apply Odd_1
          apply ht

@[simp] theorem Odd_5 :
  Odd 5 :=
    by
      intro h
      cases h with
        | add_two t ht =>
          apply Odd_3
          apply ht

/- 1.3. Complete the following proof by structural induction. -/


theorem Even_two_times :
  ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 =>
  by
    simp [mul_add]
    have even_2m : Even (2*m) :=
      Even_two_times m
    exact Even.add_two _ even_2m



/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop
  where
    | up (s r : ℕ) : s > r → ServAhead (s – r)
    | advServ : ServAhead Score.advServ
    | gameServ : ServAhead Score.gameServ
  -- enter the missing cases here

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
  ServAhead (Score.vs m n) := by
    exact ServAhead.up m n hgt

theorem ServAhead_advServ :
  ServAhead Score.advServ :=by
    exact ServAhead.advServ

theorem not_ServAhead_advRecv :
  ¬ ServAhead Score.advRecv := by
    intro h
    cases h

theorem ServAhead_gameServ :
  ServAhead Score.gameServ := by
    exact ServAhead.gameServ

theorem not_ServAhead_gameRecv :
  ¬ ServAhead Score.gameRecv :=
  by
    intro h
    cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- enter your answer here


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
  ∀t : Tree α, IsFull (mirror t) → IsFull t :=
    by
      intro tree ht
      induction tree with
        | nil =>
          apply ht
        | node a l r ih_l ih_r =>
          cases ht with
            | node =>
              apply IsFull.node
              {
                apply ih_l
                exact hr
              }
              {
                apply ih_r
                exact hl
              }
              {
                apply Iff.intro
                {
                  intro heq
                  have rightHiff := hiff.mpr
                  have kd : mirror l = Tree.nil :=
                    by
                      rw [heq]
                      rfl
                  have mirrorNil : mirror r = Tree.nil :=
                    by
                      apply rightHiff
                      exact kd
                  have treeNil := mirror_Eq_nil_Iff r
                  apply treeNil.mp
                  exact mirrorNil
                }
                {
                  intro heq
                  have leftHiff := hiff.mp
                  have kd : mirror r = Tree.nil :=
                    by
                      rw [heq]
                      rfl
                  have mirrorNil : mirror l = Tree.nil :=
                    by
                      apply leftHiff
                      exact kd
                  have treeNil := mirror_Eq_nil_Iff l
                  apply treeNil.mp
                  exact mirrorNil
                }
              }



/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β
  | Tree.nil => Tree.nil
  | Tree.node a l r => Tree.node (f a) (Tree.map f l) (Tree.map f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
  ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil :=
  by
    intro h
    cases h with
     | nil => simp [Tree.map]
     | node a l r =>
     -- Sometimes these work and I dont know exactly why. Kinda wanna rewrite these more expliclty
        simp [Tree.map]


/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem map_mirror {α β : Type} (f : α → β) :
  ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  sorry

end LoVe
