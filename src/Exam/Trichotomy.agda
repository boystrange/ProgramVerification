module Exam.Trichotomy where

open import Library.Nat
open import Library.LessThan
open import Library.Equality

data Trichotomy (x y : ℕ) : Set where
  LT : x < y  -> Trichotomy x y
  EQ : x == y -> Trichotomy x y
  GT : y < x  -> Trichotomy x y

trichotomy : (x y : ℕ) -> Trichotomy x y
trichotomy zero zero = EQ refl
trichotomy zero (succ y) = LT (le-succ le-zero)
trichotomy (succ x) zero = GT (le-succ le-zero)
trichotomy (succ x) (succ y) with trichotomy x y
... | LT p = LT (le-succ p)
... | EQ refl = EQ refl
... | GT p = GT (le-succ p)
