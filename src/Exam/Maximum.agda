module Exam.Maximum where

open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Equality
open import Library.Logic
open import Library.Logic.Laws
open import Library.LessThan

data _∈_ {A : Set} : A -> List A -> Set where
  ∈-here : (x : A) (xs : List A) -> x ∈ (x :: xs)
  ∈-next : {x y : A} {xs : List A} -> x ∈ xs -> x ∈ (y :: xs)

maximum : List ℕ -> ℕ
maximum [] = 0
maximum (x :: xs) = max x (maximum xs)

max-le-l : (x y : ℕ) -> x <= max x y
max-le-l zero y = le-zero
max-le-l (succ x) zero = le-refl
max-le-l (succ x) (succ y) = le-succ (max-le-l x y)

max-le-r : (x y : ℕ) -> y <= max x y
max-le-r zero y = le-refl
max-le-r (succ x) zero = le-zero
max-le-r (succ x) (succ y) = le-succ (max-le-r x y)

max-either : (x y : ℕ) -> x == max x y ∨ y == max x y
max-either zero zero = inl refl
max-either zero (succ y) = inr refl
max-either (succ x) zero = inl refl
max-either (succ x) (succ y) with max-either x y
... | inl p = inl (cong succ p)
... | inr p = inr (cong succ p)

maximum-le : {x : ℕ} {xs : List ℕ} -> x ∈ xs -> x <= maximum xs
maximum-le (∈-here x xs) = max-le-l x (maximum xs)
maximum-le (∈-next {_} {y} {xs} p) = le-trans (maximum-le p) (max-le-r y (maximum xs))

