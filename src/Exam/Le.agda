module Exam.Le where

open import Library.Nat
open import Library.LessThan
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality

lem : (x y : ℕ) -> ¬ (succ x <= succ y) -> ¬ (x <= y)
lem x y nle le = nle (le-succ le)

ex1 : (x y : ℕ) -> ¬ (x <= y) -> y < x
ex1 zero y nle = ex-falso (nle le-zero)
ex1 (succ x) zero nle = le-succ le-zero
ex1 (succ x) (succ y) nle = le-succ (ex1 x y (lem x y nle))

ex2 : (x y : ℕ) -> (∃[ z ] x + z == y) -> x <= y
ex2 zero y (z , eq) = le-zero
ex2 (succ x) (succ .(x + z)) (z , refl) = le-succ (ex2 x (x + z) (z , refl))
