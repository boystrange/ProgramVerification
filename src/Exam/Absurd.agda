module Exam.Absurd where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality

lem1 : (x y : ℕ) -> succ (x + succ y) == succ (succ (x + y))
lem1 x y = cong succ (symm (+-succ x y))

lem2 : (x y : ℕ) -> ¬ (succ (succ (x + y)) == 1)
lem2 x y ()

abs : ¬ (∃[ x ] ∃[ y ] 0 != x ∧ 0 != y ∧ x + y == 1)
abs (zero , y , p , q , r) = ex-falso (p refl)
abs (succ x , zero , p , q , r) = ex-falso (q refl)
abs (succ x , succ y , _ , _ , eq) = lem2 x y (tran (symm (lem1 x y)) eq)
