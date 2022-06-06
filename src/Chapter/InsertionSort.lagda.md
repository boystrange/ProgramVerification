---
---

```agda
module Chapter.InsertionSort (A : Set) (_≼_ : A -> A -> Set) where

open import Fun
open import List
open import List.Sorted A _≼_
open import List.Properties
open import List.Permutation
open import Equality
open import Unit
open import Sum
open import Product
open import Logic
open import TotalOrder A _≼_

module Extrinsic where

  insert : A -> List A -> List A
  insert x [] = x :: []
  insert x (y :: ys) with ≼total x y
  ... | left  x≼y = x :: y :: ys
  ... | right y≼x = y :: insert x ys

  insert-sort : List A -> List A
  insert-sort [] = []
  insert-sort (x :: xs) = insert x (insert-sort xs)

  all-insert : {x : A} {xs : List A} {P : A -> Set} -> P x -> all P xs -> all P (insert x xs)
  all-insert {_} {[]} p ps = p , <>
  all-insert {x} {y :: xs} p (q , ps) with ≼total x y
  ... | left  x≼y = p , q , ps
  ... | right y≼x = q , all-insert p ps

  sorted-insert-sorted : (x : A) (xs : List A) -> Sorted xs -> Sorted (insert x xs)
  sorted-insert-sorted x [] p = <> , <>
  sorted-insert-sorted x (y :: ys) (y≼ , ys-sorted) with ≼total x y
  ... | left  x≼y = (x≼y , all-all (y ≼_) (x ≼_) (≼trans x≼y) y≼) , y≼ , ys-sorted
  ... | right y≼x = all-insert y≼x y≼ , sorted-insert-sorted x ys ys-sorted

  insert-sort-sorted : (xs : List A) -> Sorted (insert-sort xs)
  insert-sort-sorted [] = <>
  insert-sort-sorted (x :: xs) =
    sorted-insert-sorted x (insert-sort xs) (insert-sort-sorted xs)

  insert-permutation : (x : A) (xs : List A) -> x :: xs # insert x xs
  insert-permutation x [] = #refl
  insert-permutation x (y :: ys) with ≼total x y
  ... | left  x≼y = #refl
  ... | right y≼x =
    #begin
      x :: y :: ys     #⟨ #swap ⟩
      y :: x :: ys     #⟨ #cong (insert-permutation x ys) ⟩
      y :: insert x ys
    #end

  insert-sort-permutation : (xs : List A) -> xs # insert-sort xs
  insert-sort-permutation [] = #refl
  insert-sort-permutation (x :: xs) =
    #begin
      x :: xs                   #⟨ #cong (insert-sort-permutation xs) ⟩
      x :: insert-sort xs       #⟨ insert-permutation x (insert-sort xs) ⟩
      insert x (insert-sort xs)
    #end

module Intrisic where

  insert : (x : A) (xs : List A) -> Sorted xs -> ∃[ ys ] x :: xs # ys ∧ Sorted ys
  insert x [] psorted = [ x ] , #refl , <> , <>
  insert x (y :: xs) (y≼*xs , psorted) with ≼total x y
  ... | left x≼y = ( x :: y :: xs
                   , #refl
                   , ( x≼y , all-all (y ≼_) (x ≼_) (≼trans x≼y) y≼*xs)
                   , y≼*xs
                   , psorted )
  ... | right y≼x with insert x xs psorted
  ... | ys , π , ysorted = y :: ys , #trans #swap (#cong π) , #all (y ≼_) π (y≼x , y≼*xs) , ysorted

  insert-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
  insert-sort [] = [] , #refl , <>
  insert-sort (x :: xs) with insert-sort xs
  ... | ys , π , ysorted with insert x ys ysorted
  ... | zs , π' , zsorted = zs , #trans (#cong π) π' , zsorted

```
