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
  assume ha: a

  show a from ha

theorem K (a b : Prop) :
  a → b → b :=

  assume ha: a
  assume hb: b

  show b from
    hb

theorem C (a b c : Prop) :
  (a → b → c) → b → a → c :=

  assume h_abc: a → b → c
  assume h_b: b
  assume h_a: a

  show c from
    h_abc h_a h_b

theorem proj_fst (a : Prop) :
  a → a → a :=

  assume ha: a
  assume ha2: a

  show a from ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
  a → a → a :=

  assume ha: a
  assume ha2: a

  show a from ha2

theorem some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=

  assume h_abc : a -> b -> c
  assume h_a : a
  assume h_ac : a -> c
  assume h_b : b

  show c from
    h_abc h_a h_b

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=

  assume h_ab : a -> b
  assume h_nb : ¬ b

  assume h_a : a

  -- show False from
  have h_b := h_ab h_a
  h_nb h_b

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=

  have h_nec: (∀x, p x ∧ q x) -> (∀x, p x) ∧ (∀x, q x) :=
    assume h_pnq: ∀x, p x ∧ q x
    show (∀x, p x) ∧ (∀x, q x) from
      have h_p: ∀x, p x :=
        fix x: α
        And.left (h_pnq x)

      have h_q: ∀x, q x :=
        fix x: α
        And.right (h_pnq x)

      And.intro h_p h_q

  have h_suf: (∀x, p x) ∧ (∀x, q x) -> (∀x, p x ∧ q x) :=
    assume hp_hq: (∀x, p x) ∧ (∀x, q x)
    show (∀x, p x ∧ q x) from
      have h_p := And.left hp_hq
      have h_q := And.right hp_hq

      fix x : α
      And.intro (h_p x) (h_q x)

  Iff.intro h_nec h_suf

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
  (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  -- fun h y' =>
  --   match h with
  --   | ⟨x, h⟩ => ⟨x, h y'⟩
  assume h: ∃x, ∀y, p x y
  fix y': α

  Exists.elim h (
    fix ex: α
    assume hxx : ∀ (y: α), p ex y
    Exists.intro ex (hxx y')
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
    (a + b) * (a + b) = a * (a + b) + b * (a + b) := by
      rw [add_mul]
    _ = a * a + a * b + b * a + b * b := by
      rw [mul_add, mul_add, ← add_assoc]
    _ = a * a + 2 * a * b + b * b := by
      rw [mul_comm b _, add_comm, add_assoc, ← Nat.two_mul (a * b), ← add_assoc]
      ac_rfl

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
  (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  -- MALAS
  sorry


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∀x : α, x = t ∧ P x) ↔ P t

lemma All.one_point_wrong_contradiction:
  ∀ (α : Type) (t : α) (P : α → Prop),
  (∃ x, ¬x = t) → ¬(∀ (x : α), x = t ∧ P x)
:=
  assume α: Type
  assume t: α
  assume P: α -> Prop

  assume h_non_ex: ∃x: α, ¬(x = t)
  assume h_absurd: (∀x : α, x = t ∧ P x)

  Exists.elim h_non_ex (
    fix x: α
    assume h_x :  ¬(x = t)

    have h_absurd_x := h_absurd x
    have h_eq_x := h_absurd_x.left

    h_x h_eq_x
  )

theorem All.proof_of_False :
  False
:=
  let top : Bool -> Prop := fun _ => True
  have h := All.one_point_wrong true top
  have h_suf := h.mpr
  have h_eq: top true := by simp
  have h_x := h_suf h_eq false
  have h_x_absurd := h_x.left

  have is_absurd: False := by
    simp at h_x_absurd

  is_absurd

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
  (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
  False :=
  sorry

end LoVe
