/- Copyright © 2018–2024 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe Exercise 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Reverse of a List

We define an accumulator-based variant of `reverse`. The first argument, `as`,
serves as the accumulator. This definition is __tail-recursive__, meaning that
compilers and interpreters can easily optimize the recursion away, resulting in
more efficient code. -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

#eval 1 :: [2, 3]
#eval reverseAccu [] [1, 2, 3]
#eval reverseAccu [1] [2, 3]
#eval reverseAccu [] [2, 3] ++ reverseAccu [] [1]

/- 1.1. Our intention is that `reverseAccu [] xs` should be equal to
`reverse xs`. But if we start an induction, we quickly see that the induction
hypothesis is not strong enough. Start by proving the following generalization
(using the `induction` tactic or pattern matching): -/

#check reverse
#check reverseAccu
#check reverse_append

theorem reverseAccu_Eq_reverse_append {α : Type} :
  ∀as xs : List α, reverseAccu as xs = reverse xs ++ as :=
by
  intro as xs

  induction xs generalizing as with
  | nil =>          -- xs = []
    rfl
  | cons x xxs ih =>
    rw [reverseAccu, reverse]
    simp [ih]

theorem reverseAccu_Eq_reverse_append_2 {α : Type} :
  ∀as xs : List α, reverseAccu as xs = reverse xs ++ as
  | as, []        =>
    by rfl

  | as, x :: xxs   =>
    let h_ih := fun h_as => reverseAccu_Eq_reverse_append_2 h_as xxs
    let ih := h_ih (x :: as)

    by simp [reverseAccu, reverse, ih]


/- 1.2. Derive the desired equation. -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
  reverseAccu [] xs = reverse xs :=
by
  have h := reverseAccu_Eq_reverse_append [] xs
  simp at h
  assumption

/- 1.3. Prove the following property.

Hint: A one-line inductionless proof is possible. -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
  reverseAccu [] (reverseAccu [] xs) = xs :=
by
  simp [reverseAccu_eq_reverse, reverse_reverse]

/- 1.4. Prove the following theorem by structural induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how
structural induction works (and is good practice for the final exam).

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the induction hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `rfl` or `simp` need not be
justified if you think they are obvious (to humans), but you should say which
key theorems they depend on. You should be explicit whenever you use a function
definition. -/

-- enter your paper proof here


/- ## Question 2: Drop and Take

The `drop` function removes the first `n` elements from the front of a list. -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. Define the `take` function, which returns a list consisting of the first
`n` elements at the front of a list.

To avoid unpleasant surprises in the proofs, we recommend that you follow the
same recursion pattern as for `drop` above. -/

def take {α : Type} : ℕ → List α → List α :=
  fun n ls => match n, ls with
  | 0,      _       => []
  | _ + 1,  []      => []
  | m + 1,  x :: xs => x :: take m xs

#eval take 0 [3, 7, 11]   -- expected: []
#eval take 1 [3, 7, 11]   -- expected: [3]
#eval take 2 [3, 7, 11]   -- expected: [3, 7]
#eval take 3 [3, 7, 11]   -- expected: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- expected: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- expected: ["a", "b"]

/- 2.2. Prove the following theorems, using `induction` or pattern matching.
Notice that they are registered as simplification rules thanks to the `@[simp]`
attribute. -/

@[simp] theorem drop_nil {α : Type} :
  ∀n : ℕ, drop n ([] : List α) = [] :=
by
  intro n

  induction n with
  | zero => rfl
  | succ _ _ =>rfl


@[simp] theorem take_nil {α : Type} :
  ∀n : ℕ, take n ([] : List α) = [] :=
by
  intro n

  induction n with
  | zero => rfl
  | succ _ _ => rfl

/- 2.3. Follow the recursion pattern of `drop` and `take` to prove the
following theorems. In other words, for each theorem, there should be three
cases, and the third case will need to invoke the induction hypothesis.

Hint: Note that there are three variables in the `drop_drop` theorem (but only
two arguments to `drop`). For the third case, `← add_assoc` might be useful. -/

#check Ord

lemma h_drop_comm {α: Type}:
  ∀(m n: ℕ) (xs: List α),
  drop n (drop m xs) = drop m (drop n xs) :=
  sorry

lemma drop_1 {α: Type}:
  ∀(m: ℕ) (xs: List α), drop 1 (drop m xs) = drop (1 + m) xs
  | 0, xs => by rfl
  | _, [] => by simp
  | m+1, _::xs => drop_1 m xs

theorem drop_drop {α : Type} :
  ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0, n, xs => by rfl
  | m, 0, xs => by simp; rfl
  | m', n'+1, xs => by
    -- Induction Hypothesis:
    -- Forall h_m: N // h_m <= m', h_n: N, h_ls: List α ,
    --    drop h_n (drop n' h_ls) = drop (n' + h_n) h_ls
    -- have h_ih := fun (h_n: ℕ) (h_ls: List α) => drop_drop m' h_n h_ls
    have ih:
      ∀(m n: ℕ) (xs: List α),
      n < n'+1 → drop n (drop m xs) = drop (n + m) xs :=
      fun m n xs _ =>
        drop_drop m n xs

    have h_m_1: drop 1 (drop m' xs) = drop (1 + m') xs :=
      drop_1 m' xs

    have h_simp := calc
      drop (n' + 1) (drop m' xs) = drop n' (drop 1 (drop m' xs)) := by
        apply Eq.symm
        exact ih 1 n' (drop m' xs) (by simp)

      _ = drop n' (drop (1 + m') xs) := by
        rw [h_m_1]

      _ = drop (n' + 1 + m') xs := by
        have h := ih (1 + m') n' xs (by simp)
        rw [add_assoc]

        exact h

    exact h_simp


theorem drop_drop_2 {α : Type} :
  ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0, n, xs => by simp [drop]
  | _, n, [] => by simp [drop]
  | m+1, n, _::xs =>
    have IH := drop_drop m n xs
    by simp [drop, IH]

theorem take_take {α : Type} :
  ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
  | 0, _ => by simp [take]
  | _, [] => by simp [take]
  | m+1, _ :: xs => by
    have ih := take_take m xs
    simp [take, ih]

theorem take_drop {α : Type} :
  ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs
  | 0, _ => by rfl
  | _, [] => by simp
  | n+1, x::xs => by
    have ih := take_drop n xs
    simp [take, drop, ih]

/- ## Question 3: A Type of Terms

3.1. Define an inductive type corresponding to the terms of the untyped
λ-calculus, as given by the following grammar:

    Term  ::=  `var` String        -- variable (e.g., `x`)
            |  `lam` String Term   -- λ-expression (e.g., `λx. t`)
            |  `app` Term Term     -- application (e.g., `t u`) -/

-- enter your definition here
inductive Term: Type where
| var: String -> Term
| lam: String -> Term -> Term
| app: Term -> Term -> Term

/- 3.2 (**optional**). Register a textual representation of the type `term` as
an instance of the `Repr` type class. Make sure to supply enough parentheses to
guarantee that the output is unambiguous. -/

def Term.repr : Term → String
| var x => x
| lam x t => "(λ" ++ x ++ ". " ++ repr t ++ ")"
| app t u => "(" ++ repr t ++ " " ++ repr u ++ ")"


instance Term.Repr : Repr Term :=
  { reprPrec := fun t prec ↦ Term.repr t }

/- 3.3 (**optional**). Test your textual representation. The following command
should print something like `(λx. ((y x) x))`. -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
