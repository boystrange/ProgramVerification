module Lab.Lab1-begin where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Equality
open import Library.Equality.Reasoning

-- define two functions to establish whether a natural number is
-- even or odd, respectively. make sure that each function is
-- defined recursively by case analysis on its argument. In
-- particular, do *not* define odd as the negation of even nor even
-- as the negation of odd

even : ℕ -> Bool
even = {!!}

odd : ℕ -> Bool
odd = {!!}

-- prove the theorem even-not-odd

even-not-odd : ∀(x : ℕ) -> even x == not (odd x)
even-not-odd = {!!}

-- prove the theorem not-even-odd without using recursion/induction

not-even-odd : ∀(x : ℕ) -> not (even x) == odd x
not-even-odd = {!!}

-- prove that x + x is always even

twice-even : ∀(x : ℕ) -> even (x + x) == true
twice-even = {!!}

-- prove that 2 * x is always even without using case analysis

two-times-even : ∀(x : ℕ) -> even (2 * x) == true
two-times-even = {!!}

-- define a function sum : ℕ -> ℕ such that sum n is the sum of the
-- first n natural numbers. check that the function works correctly
-- using C-c C-n

sum : ℕ -> ℕ
sum = {!!}

-- prove that the Gauss formula is correct

gauss : ∀(x : ℕ) -> 2 * sum x == x * succ x
gauss = {!!}
