/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe Exercise 10: Hoare Logic

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Program Verification

1.1. The following WHILE program takes two numbers `a` and `b` and increments
`b` until it reaches `a`: -/

def COUNT_UP : Stmt :=
  Stmt.whileDo (fun s ↦ s "b" ≠ s "a")
    (Stmt.assign "b" (fun s ↦ s "b" + 1))

/- Prove the following Hoare triple. The main difficulty is to figure out which
invariant to use for the while loop. The invariant should capture both the work
that has been done already (the intermediate result) and the work that remains
to be done. Use a `show` command to annotate the program with a loop invariant.

Hint: If a variable `x` does not change in a program, it might be useful to
record this in the invariant, by adding a conjunct `s "x" = x₀`. -/

theorem COUNT_UP_correct (a₀ : ℕ) :
  {* fun s ↦ s "a" = a₀ *} (COUNT_UP) {* fun s ↦ s "a" = a₀ ∧ s "b" = a₀ *} :=
  -- apply the while intro and adding conjunct `s "a" = a₀`
  PartialHoare.while_intro' (fun s ↦ s "a" = a₀)
  (by
    apply PartialHoare.assign_intro'
    simp [*]
    intro s h _
    exact h
  )
  (by
    intro s ha
    apply ha
  )
  (by
    intro s hB hI
    apply And.intro
    {
      exact hI
    }
    {
      aesop
    }
  )


/- 1.2. What happens if the program is run with `b > a`? How is this captured
by the Hoare triple? -/

-- enter your solution here

/- 1.3. The following WHILE program is intended to compute the Gaussian sum up
to `n`, leaving the result in `r`. -/

def GAUSS (N : ℕ) : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.assign "n" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ N)
    (Stmt.assign "n" (fun s ↦ s "n" + 1);
     Stmt.assign "r" (fun s ↦ s "r" + s "n"))

/- Here is a functional implementation of the same function: -/

def sumUpTo : ℕ → ℕ
  | 0     => 0
  | n + 1 => n + 1 + sumUpTo n

#eval sumUpTo 6
#eval sumUpTo 5
/- Invoke `vcg` on `GAUSS` using a suitable loop invariant and prove the
emerging verification conditions. -/

theorem GAUSS_correct (N : ℕ) :
 {* fun s ↦ True *} (GAUSS N) {* fun s ↦ s "r" = sumUpTo N *} :=
  show {* fun s ↦ True *}
     (Stmt.assign "r" (fun s ↦ 0);
      Stmt.assign "n" (fun s ↦ 0);
      ( Stmt.invWhileDo (fun s ↦ s "r" = sumUpTo (s "n"))
          (fun s ↦ s "n" ≠ N)
          (Stmt.assign "n" (fun s ↦ s "n" + 1);
          Stmt.assign "r" (fun s ↦ s "r" + s "n"))))
      {* fun s ↦ s "r" = sumUpTo N *} by
        vcg <;>
        intro s h
        {
          simp [*]
          rw [sumUpTo]
          rw [add_comm]
        }
        {
          intro mh
          rw [mh]
          aesop
        }
        {
          simp [*]
          rw [sumUpTo]
  }


/- 1.4 (**optional**). The following program `MUL` is intended to compute the
product of `n` and `m`, leaving the result in `r`. Invoke `vcg` on `MUL` using a
suitable loop invariant and prove the emerging verification conditions. -/

def MUL : Stmt :=
  Stmt.assign "r" (fun s ↦ 0);
  Stmt.whileDo (fun s ↦ s "n" ≠ 0)
    (Stmt.assign "r" (fun s ↦ s "r" + s "m");
     Stmt.assign "n" (fun s ↦ s "n" - 1))


-- Super pain to prove
theorem MUL_correct (n₀ m₀ : ℕ) :
  {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *} (MUL) {* fun s ↦ s "r" = n₀ * m₀ *} :=
  show
    {* fun s ↦ s "n" = n₀ ∧ s "m" = m₀ *}
    (Stmt.assign "r" (fun s ↦ 0);
    Stmt.invWhileDo (fun s ↦ s "r" + s "n" * m₀ = n₀ * m₀ ∧ s "m" = m₀) (fun s ↦ s "n" ≠ 0)
      (Stmt.assign "r" (fun s ↦ s "r" + s "m");
      Stmt.assign "n" (fun s ↦ s "n" - 1)))
    {* fun s ↦ s "r" = n₀ * m₀ *} by
    vcg <;>
    intro s h
    have hLeft := h.left.left
    have hRight := h.right
    (
      -- Continue to rewrite our equation to match both sides
      simp [*]
      rw [mul_comm]
      rw [Nat.mul_sub_left_distrib]
      simp [*]
      rw [← Nat.add_sub_assoc]
      rw [Nat.sub_add_comm]
      simp [*]
      rw [mul_comm]
      rw [← hLeft]
      aesop
    )
    (
      -- we can show that the s "n" has to be grater than zero since its a natural number and not
      -- equal to zero from hRight
      have nGreater : s "n" > 0 :=
        by
          apply Nat.pos_of_ne_zero
          exact hRight
      -- SHow that m₀ is less than or equal to m₀ * s "n" since n is greater than zero
      have mEqual : m₀ * 1 ≤ m₀ * s "n" := Nat.mul_le_mul_left m₀ nGreater
      have tt : m₀ =m₀ * Nat.succ 0 :=
        by
          simp [*]
      -- Rewrite our equality to match mEqual
      rw [tt]
      rw [Nat.succ_eq_add_one]
      rw [Nat.zero_add]
      rw [mul_assoc]
      rw [one_mul]
      exact mEqual
    )
    (
      simp [*]
      intro h3 h4
      -- can show s "n" = 0 from h : ¬s "n" ≠ 0
      have hn : s "n" = 0 :=
        by
          contrapose! h
          exact h
      -- we need a way to rewrite s "r" and isolate it so show that
      -- s "r" is equal to n₀ * m₀ - (s "m" * m₀)
      have h5 : s "r" = n₀ * m₀ - (s "n" * m₀) :=
        by
          rw [← h3]
          rw [hn]
          rw [zero_mul]
          simp

      rw [h5]
      rw [hn]
      rw [← mul_comm]
      rw [zero_mul]
      rfl
    )
    (
      -- Use simp I guess
      simp [*]
    )


/- ## Question 2: Hoare Triples for Total Correctness

The following definition captures Hoare triples for total correctness for
deterministic languages: -/

def TotalHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s, P s → ∃t, (S, s) ⟹ t ∧ Q t

macro "[*" P:term " *] " "(" S:term ")" " [* " Q:term " *]" : term =>
  `(TotalHoare $P $S $Q)

namespace TotalHoare

/- 2.1. Prove the consequence rule. -/

theorem consequence {P P' Q Q' S}
    (hS : [* P *] (S) [* Q *]) (hP : ∀s, P' s → P s) (hQ : ∀s, Q s → Q' s) :
  [* P' *] (S) [* Q' *] :=
  sorry


/- 2.2. Prove the rule for `skip`. -/

theorem skip_intro {P} :
  [* P *] (Stmt.skip) [* P *] :=
  sorry

/- 2.3. Prove the rule for `assign`. -/

theorem assign_intro {P x a} :
  [* fun s ↦ P (s[x ↦ a s]) *] (Stmt.assign x a) [* P *] :=
  sorry

/- 2.4. Prove the rule for `seq`. -/

theorem seq_intro {P Q R S T} (hS : [* P *] (S) [* Q *])
  (hT : [* Q *] (T) [* R *]) :
  [* P *] (S; T) [* R *] :=
  sorry

/- 2.5. Complete the proof of the rule for `if`–`then`–`else`.

Hint: The proof requires a case distinction on the truth value of `B s`. -/

theorem if_intro {B P Q S T}
    (hS : [* fun s ↦ P s ∧ B s *] (S) [* Q *])
    (hT : [* fun s ↦ P s ∧ ¬ B s *] (T) [* Q *]) :
  [* P *] (Stmt.ifThenElse B S T) [* Q *] :=
  sorry

/- 2.6 (**optional**). Try to prove the rule for `while`.

The rule is parameterized by a loop invariant `I` and by a variant `V` that
decreases with each iteration of the loop body.

Before we prove the desired theorem, we introduce an auxiliary theorem. Its
proof requires induction by pattern matching and recursion. When using
`var_while_intro_aux` as induction hypothesis we recommend to do it directly
after proving that the argument is less than `v₀`:

    have ih : ∃u, (stmt.while b S, t) ⟹ u ∧ I u ∧ ¬ b u :=
      have _ : V t < v₀ :=
        …
      var_while_intro_aux I V h_inv (V t) …

Similarly to `if`--`then`--`else`, the proof requires a case distinction on the
truth value of `B s`. -/

theorem var_while_intro_aux {B} (I : State → Prop) (V : State → ℕ) {S}
  (h_inv : ∀v₀,
     [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
  ∀v₀ s, V s = v₀ → I s → ∃t, (Stmt.whileDo B S, s) ⟹ t ∧ I t ∧ ¬ B t
  | v₀, s, V_eq, hs =>
    sorry

theorem var_while_intro {B} (I : State → Prop) (V : State → ℕ) {S}
  (hinv : ∀v₀,
     [* fun s ↦ I s ∧ B s ∧ V s = v₀ *] (S) [* fun s ↦ I s ∧ V s < v₀ *]) :
  [* I *] (Stmt.whileDo B S) [* fun s ↦ I s ∧ ¬ B s *] :=
  sorry

end TotalHoare

end LoVe
