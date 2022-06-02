open import TotalOrder

module List.Sorted (A : Set) (ord : TotalOrder A) where

open import List
open import Logic
open TotalOrder.TotalOrder ord

infix 4 _≼*_ _*≼_

_≼*_ : A -> List A -> Set
x ≼* xs = all (x ≼_) xs

_*≼_ : List A -> A -> Set
xs *≼ x = all (_≼ x) xs

Sorted : List A -> Set
Sorted [] = ⊤
Sorted (x :: xs) = x ≼* xs ∧ Sorted xs
