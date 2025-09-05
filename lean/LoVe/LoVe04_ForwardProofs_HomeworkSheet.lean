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
  fix a: Prop
  fix b: Prop

  assume h₁ : ¬ a ∨ b
  assume h₂ : a

  Or.elim h₁
    ( assume h_na: ¬ a

      have h_f := h_na h₂
      False.elim h_f )
    ( assume h_b: b
      h_b )


/- 1.2 (2 points). Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
  ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a: Prop
  fix b: Prop

  assume h₁ : ¬ a ∨ b
  assume h₂ : a

  Or.elim h₁
    ( assume h_na: ¬ a

      have h_f := h_na h₂
      False.elim h_f )
    ( assume h_b: b
      h_b )


/- ## Question 2 (6 points): Connectives and Quantifiers

2.1 (3 points). Supply a structured proof of the commutativity of `∨` under a
`∀` quantifier, using no other theorems than the introduction and elimination
rules for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
  (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=

  have h_nec : (∀x, p x ∨ q x) → (∀x, q x ∨ p x) :=
    assume h: ∀x, p x ∨ q x

    fix x': α

    have h_pq: p x' ∨ q x' := h x'

    Or.elim h_pq
      ( assume h_p: p x'
        Or.inr h_p )
      ( assume h_q: q x'
        Or.inl h_q )

  have h_suf : (∀x, q x ∨ p x) → (∀x, p x ∨ q x) :=
    assume h: (∀x, q x ∨ p x)

    fix x': α

    have h_qp : q x' ∨ p x' :=
      h x'

    Or.elim h_qp
      ( assume h_q: q x'
        Or.inr h_q )
      ( assume h_p: p x'
        Or.inl h_p )

  Iff.intro h_nec h_suf

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
  assume dn: DoubleNegation

  have em: ExcludedMiddle := SorryTheorems.EM_of_DN dn

  Peirce_of_EM em

theorem EM_of_Peirce :
  Peirce → ExcludedMiddle :=

  assume p: Peirce

  have dn: DoubleNegation := DN_of_Peirce p

  SorryTheorems.EM_of_DN dn

theorem dn_of_em :
  ExcludedMiddle → DoubleNegation :=

  assume em: ExcludedMiddle

  have p: Peirce := Peirce_of_EM em

  DN_of_Peirce p

end BackwardProofs

end LoVe
