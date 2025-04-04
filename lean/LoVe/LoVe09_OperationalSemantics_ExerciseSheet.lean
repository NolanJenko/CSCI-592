/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe Exercise 9: Operational Semantics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Guarded Command Language

In 1976, E. W. Dijkstra introduced the guarded command language (GCL), a
minimalistic imperative language with built-in nondeterminism. A grammar for one
of its variants is given below:

    S  ::=  x := e       -- assignment
         |  assert B     -- assertion
         |  S ; S        -- sequential composition
         |  S | ⋯ | S    -- nondeterministic choice
         |  loop S       -- nondeterministic iteration

Assignment and sequential composition are as in the WHILE language. The other
statements have the following semantics:

* `assert B` aborts if `B` evaluates to false; otherwise, the command is a
  no-op.

* `S | ⋯ | S` chooses any of the branches and executes it, ignoring the other
  branches.

* `loop S` executes `S` any number of times.

In Lean, GCL is captured by the following inductive type: -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. Complete the following big-step semantics, based on the informal
specification of GCL above. -/

inductive BigStep : (Stmt × State) → State → Prop
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- enter the missing `seq` rule here
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  -- below, `Ss[i]'hless` returns element `i` of `Ss`, which exists thanks to
  -- condition `hless`
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- enter the missing `loop` rules here
  | loop (S s t u)
    (hOne : BigStep (S, s) t) (hTwo : BigStep (Stmt.loop S, t) u):
    BigStep (Stmt.loop S, s) u
  | loop_base (S s) :
    BigStep (Stmt.loop S, s) s


infixl:110 " ⟹ " => BigStep

/- 1.2. Prove the following inversion rules, as we did in the lecture for the
WHILE language. -/
-- Easy since they are exactly the same for assignment
@[simp] theorem BigStep_assign_iff {x a s t} :
  (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
    by
    apply Iff.intro
    { intro h
      cases h with
        | assign f g =>
          rfl
    }
    { intro h
      rw [h]
      apply BigStep.assign
    }


@[simp] theorem BigStep_assert {B s t} :
  (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
  by
    apply Iff.intro
      (
        by
          intro h
          cases h with
            | assert =>
              apply And.intro
              (
                rfl
              )
              (
                exact hB
              )
      )
      (
        by
          intro h
          cases h with
            | intro =>
              rw [left]
              apply BigStep.assert
              exact right
      )


@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
  (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
    by
    -- Just copied the Bigstep seq iff from the demo since both seq have the
    -- same bigstep notation
    apply Iff.intro
    { intro h
      cases h with
      | seq =>
        apply Exists.intro
        apply And.intro <;>
          assumption }
    { intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.seq <;>
            assumption }

theorem BigStep_loop {S s u} :
  (Stmt.loop S, s) ⟹ u ↔
  (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  by
  apply Iff.intro
   (by
      intro h
      cases h with
        | loop =>
          apply Or.inr
          -- Can techically use aesop here to finish the proof but that feels a bit cheap
          apply Exists.intro
          {
            apply And.intro hOne
            {
              exact hTwo
            }
          }
        | loop_base =>
          apply Or.inl
          rfl
   )
   (
    by
      intro h
      cases h with
        | inr =>
          apply Exists.elim h_1
          {
            intro t hElim
            cases hElim with
              | intro =>
                apply BigStep.loop
                apply left
                exact right
          }
        | inl =>
          simp [h_1]
          simp [BigStep.loop_base S u]
   )

/- This one is more difficult: -/

@[simp] theorem BigStep_choice {Ss s t} :
  (Stmt.choice Ss, s) ⟹ t ↔
  (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
    by
      apply Iff.intro
      {
        intro h
        apply Exists.elim
        {
          apply Exists.elim
          {
            apply
          }
          {
            sorry
          }
          {
            sorry
          }

        }
        {
          sorry
        }
        {
          sorry
        }
      }
      {
        sorry
      }

end GCL

/- 1.3. Complete the translation below of a deterministic program to a GCL
program, by filling in the `sorry` placeholders below. -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    GCL.Stmt.assign x a
  | S; T =>
    GCL.Stmt.seq (gcl_of S) (gcl_of T)
  -- not maybe the best translate but an if statement becomes a nondeterminsitc execution of the inner statement
  -- or the else statement
  | Stmt.ifThenElse B S T  =>
    GCL.Stmt.choice [gcl_of S, gcl_of T]
  | Stmt.whileDo B S =>
    GCL.Stmt.loop (gcl_of S)

/- 1.4. In the definition of `gcl_of` above, `skip` is translated to
`assert (fun _ ↦ True)`. Looking at the big-step semantics of both constructs,
we can convince ourselves that it makes sense. Can you think of other correct
ways to define the `skip` case? -/

-- enter your answer here


/- ## Question 2: Program Equivalence

For this question, we introduce the notion of program equivalence: `S₁ ~ S₂`. -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- Program equivalence is an equivalence relation, i.e., it is reflexive,
symmetric, and transitive. -/

theorem BigStepEquiv.refl {S} :
  S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
  S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
  S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. Prove the following program equivalences. -/

theorem BigStepEquiv.skip_assign_id {x} :
  Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
    fix s t : State
    show (Stmt.assign x fun s => s x, s) ⟹ t ↔ (Stmt.skip, s) ⟹ t from
      Iff.intro
      (
        assume h : (Stmt.assign x fun s => s x, s) ⟹ t
        show (Stmt.skip, s) ⟹ t from
          by
            cases h with
              | assign =>
                simp
      )
        (
          assume h : (Stmt.skip, s) ⟹ t
          show (Stmt.assign x fun s => s x, s) ⟹ t from
            by
              cases h with
                | skip => simp
        )


theorem BigStepEquiv.seq_skip_left {S} :
  Stmt.skip; S ~ S :=
    fix s t : State
    Iff.intro
      (
        assume h : (Stmt.skip; S, s) ⟹ t
        show (S, s) ⟹ t from
          by
            cases h with
              | seq =>
                aesop
      )
      (assume h : (S, s) ⟹ t
      by
        apply BigStep.seq _ _ _ s t
        apply BigStep.skip s
        exact h
    )

theorem BigStepEquiv.seq_skip_right {S} :
  S; Stmt.skip ~ S :=
    fix s t : State
    Iff.intro
     (
      assume h : (S; Stmt.skip, s) ⟹ t
      show (S, s) ⟹ t from
        by
          cases h with
            | seq d m f t=>
              exact hS
     )
     (
      -- Backwards proof
      -- by
      --   intro h
      --   apply BigStep.seq
      --   apply h
      --   apply BigStep.skip
      -- Forwards Proof
      assume h: (S, s) ⟹ t
      have hSkip : (Stmt.skip, t) ⟹ t :=
        BigStep.skip t
      have hSeq :=
        BigStep.seq S Stmt.skip s t t
      hSeq h hSkip
     )

theorem BigStepEquiv.if_seq_while_skip {B S} :
  Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
  sorry

/- 2.2 (**optional**). Program equivalence can be used to replace subprograms
by other subprograms with the same semantics. Prove the following so-called
congruence rules that facilitate such replacement: -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
    (hT : T₁ ~ T₂) :
  S₁; T₁ ~ S₂; T₂ :=
  by
    intro s t
    apply Iff.intro
      (
        by
          intro h

      )
      {

      }

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
  Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  sorry

end LoVe
