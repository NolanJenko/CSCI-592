/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Homework must be done individually.

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Snoc

1.1 (3 points). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

def snoc {α : Type} : List α → α → List α
  | [], a => [a]
  | x::xs, a => x :: snoc xs a

/- 1.2 (1 point). Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

#eval snoc [1] 2
#eval snoc [1,2,3] 8
-- invoke `#eval` or `#reduce` here


/- ## Question 2 (6 points): Sum

2.1 (3 points). Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List ℕ → ℕ
  | [] => 0
  | x::xs => x + (sum xs)

#eval sum [1, 12, 3]   -- expected: 16

/- 2.2 (3 points). State (without proving them) the following properties of
`sum` as theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here
theorem listSnocEquality (a : ℕ) (lst : List ℕ) :
  sum (snoc lst a) = a + sum lst :=
    sorry

theorem listAppendEquality (lstOne : List ℕ) (lstTwo : List ℕ ) :
  sum (lstOne ++ lstTwo) = sum lstOne + sum lstTwo :=
    sorry

theorem reverseListEquality (lst : List ℕ ) :
  sum (reverse lst) = sum lst :=
    sorry


end LoVe
