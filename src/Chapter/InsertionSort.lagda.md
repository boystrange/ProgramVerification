---
---

```agda
module Chapter.InsertionSort
  (A : Set)
  (_≼_ : A -> A -> Set)
  where

open import Fun
open import List
open import List.Sorted A _≼_
open import List.Properties
open import List.Permutation
open import Equality
open import Logic
-- open import TotalOrder A _≼_

postulate
  ≼trans : {x y z : A} -> (x ≼ y) -> (y ≼ z) -> (x ≼ z)
  ≼total : (x y : A) -> (x ≼ y) ∨ (y ≼ x)

module Intrisic where

  insert : (x : A) (xs : List A) -> Sorted xs -> ∃[ ys ] x :: xs # ys ∧ Sorted ys
  insert x [] psorted = [ x ] , #refl , <> , <>
  insert x (y :: xs) (y≼*xs , psorted) with ≼total x y
  ... | inl x≼y = ( x :: y :: xs
                   , #refl
                   , ( x≼y , all-all (y ≼_) (x ≼_) (≼trans x≼y) y≼*xs)
                   , y≼*xs
                   , psorted )
  ... | inr y≼x with insert x xs psorted
  ... | ys , π , ysorted = y :: ys , #trans #swap (#cong π) , #all (y ≼_) π (y≼x , y≼*xs) , ysorted

  insert-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
  insert-sort [] = [] , #refl , <>
  insert-sort (x :: xs) with insert-sort xs
  ... | ys , π , ysorted with insert x ys ysorted
  ... | zs , π' , zsorted = zs , #trans (#cong π) π' , zsorted

```
