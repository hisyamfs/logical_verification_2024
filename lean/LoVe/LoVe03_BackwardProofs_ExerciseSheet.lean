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
    exact ha

theorem K (a b : Prop) :
  a → b → b :=
  by
    intro
    intro hb
    exact hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=
  by
    intro hab hb ha
    apply hab
    apply ha
    exact hb

theorem proj_fst (a : Prop) :
  a → a → a :=
  by
    intro ha1 ha2
    exact ha1

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
  a → a → a :=
  by
    intro ha1 ha2
    exact ha2

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
  by
    intro hab ha hha hb
    apply hha
    exact ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
  by
    intro hha hnb
    intro ha
    apply hnb
    exact (hha ha)

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    -- case mp
    { intro h_pq
      apply And.intro
      { intro hx
        exact And.left (h_pq hx) }
      { intro hx
        exact And.right (h_pq hx)} }
    -- case mpr
    { apply And.elim
      intro hp hq
      intro hx
      exact And.intro (hp hx) (hq hx) }


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

theorem mul_zero (n : ℕ) :
  mul 0 n = 0 :=
  by
    induction n with
    | zero        => rfl
    | succ n' ih  => simp [mul, ih]; rfl

#check add_succ

theorem mul_succ (m n : ℕ) :
  mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
    | zero => rfl
    | succ n' ih =>
      simp [mul, add, add_assoc, add_succ, ih]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
  mul m n = mul n m :=
  by
    induction n with
    | zero =>
      simp [mul, mul_zero]
    | succ n' ih =>
      simp [mul, mul_succ, add_comm, ih]
      -- simp [ih, mul, mul_succ, add_comm]
      -- simp [mul, mul_succ, add_comm, ih]

theorem mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
    | zero =>
      rfl
    | succ n' ih =>
      simp [mul, mul_add, ih]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
  by
    induction n with
    | zero =>
      rw [mul_comm, mul_zero]
      apply Eq.symm
      rw [mul_zero, mul_zero]
      rfl
    | succ n' ih =>
      rw [mul_comm, mul_succ, mul_comm, ih, add_assoc]
      apply Eq.symm
      rw [mul_succ, mul_succ, add_assoc, add_comm l _, add_assoc, add_comm m]


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

/--
  Gagal paham, tapi yaudah lah ya
-/
theorem Peirce_of_EM :
  ExcludedMiddle → Peirce :=
  by
    rw [ExcludedMiddle, Peirce]

    intro h_em h_a h_b h_peirce

    have h_em_a := h_em h_a
    have h_em_b := h_em h_b

    apply Or.elim h_em_a
    . intro hh_a
      exact hh_a
    . intro hh_na
      apply Or.elim h_em_b
      . intro hh_b
        apply False.elim
        apply hh_na
        apply h_peirce
        intro
        exact hh_b
      . intro
        apply h_peirce
        intro hh_a
        apply False.elim
        apply hh_na
        exact hh_a


/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
  Peirce → DoubleNegation :=
  sorry

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
  DoubleNegation → ExcludedMiddle :=
sorry

end SorryTheorems

end BackwardProofs

end LoVe
