module Lab.Lab2-begin where

open import Library.Fun
open import Library.Logic
open import Library.Logic.Laws
open import Library.Nat
open import Library.Equality

-- EXERCISE 1: prove the isomorphism between the types A -> B -> C
-- and A ∧ B -> C

uncurry : ∀{A B C : Set} -> (A -> B -> C) -> A ∧ B -> C
uncurry = {!!}

curry : ∀{A B C : Set} -> (A ∧ B -> C) -> A -> B -> C
curry = {!!}

-- EXERCISE 2: prove the inverse of the elimination principle of
-- disjunction ∨-elim

∨-elim-inv : ∀{A B C : Set} -> (A ∨ B -> C) -> (A -> C) ∧ (B -> C)
∨-elim-inv = {!!}

-- EXERCISE 3: in classical logic, the truth table of an implication
-- A -> B coincides with that of the proposition ¬ A ∨ B. Prove that
-- ¬ A ∨ B implies A -> B. Suggestion: it may be useful to use the
-- principle of contradiction and the principle of explosion (ex
-- falso quodlibet)

∨-imp : ∀{A B : Set} -> ¬ A ∨ B -> (A -> B)
∨-imp = {!!}

-- what kind of problem arises when trying to prove the inverse of
-- ∨-imp?

∨-imp-inv : ∀{A B : Set} -> (A -> B) -> ¬ A ∨ B
∨-imp-inv = {!!}

-- EXERCISE 4: prove that the successor of a number cannot be 0 and
-- that the successor of the successor of a number cannot be 1

succ-not-zero : ∀(x : ℕ) -> succ x != 0
succ-not-zero = {!!}

succ-succ-not-one : ∀(x : ℕ) -> succ (succ x) != 1
succ-succ-not-one = {!!}

-- EXERCISE 5: prove that every natural number is either equal to 0
-- or different from 0

zero-or-not-zero : ∀(x : ℕ) -> x == 0 ∨ x != 0
zero-or-not-zero = {!!}

-- EXERCISE 6: prove that every natural number is either 0 or 1 or
-- different from both 0 and 1

zero-or-one : ∀(x : ℕ) -> x == 0 ∨ x == 1 ∨ (x != 0 ∧ x != 1)
zero-or-one = {!!}
