module Exam.Minus where

open import Library.Nat
open import Library.Equality
open import Library.LessThan

minus-zero : (x : ℕ) -> x - 0 == x
minus-zero zero = refl
minus-zero (succ x) = refl

le-minus : {x y : ℕ} -> x <= y -> x + (y - x) == y
le-minus le-zero = minus-zero _
le-minus (le-succ le) = cong succ (le-minus le)

