---
---

```agda
module InsertionSort where

module SortedLists where

open import List
open import Permutation
open import Equality
open import Unit
open import Sum
open import Product
open import Logic
open import TotalOrder

variable A : Set

-- guardare lezioni su overloading di Peter Selinger
postulate
  _<=_ : A -> A -> Set
  total : (x y : A) -> (x <= y) ⊎ (y <= x)
  antisymmetry : (x y : A) -> x <= y -> y <= x -> x == y
  reflexivity : (x : A) -> x <= x
  transitivity : {x y z : A} -> x <= y -> y <= z -> x <= z

insert : A -> List A -> List A
insert x [] = x :: []
insert x (y :: ys) with total x y
... | left x<=y = x :: (y :: ys)
... | right y<=x = y :: insert x ys

insert-sort : List A -> List A
insert-sort [] = []
insert-sort (x :: xs) = insert x (insert-sort xs)

_<=L_ : A -> List A -> Set
x <=L [] = ⊤
x <=L (y :: ys) = (x <= y) ∧ (x <=L ys)

sorted : List A -> Set
sorted [] = ⊤
sorted (x :: xs) = (x <=L xs) ∧ sorted xs

all<= : ∀{x y : A}{xs : List A} -> x <= y -> y <=L xs -> x <=L xs
all<= {xs = []} x<=y y<= = <>
all<= {xs = z :: xs} x<=y (y<=z , y<=) = transitivity x<=y y<=z , all<= x<=y y<=

all<=-insert : ∀{x y : A}{xs : List A} -> y <= x -> y <=L xs -> y <=L insert x xs
all<=-insert {xs = []} y<=x y<= = y<=x , <>
all<=-insert {_} {x} {_} {z :: xs} y<=x (y<=z , y<=) with total x z
... | left x<=z = y<=x , (y<=z , y<=)
... | right z<=x = y<=z , all<=-insert y<=x y<=

sorted-insert-sorted : (x : A) (xs : List A) -> sorted xs -> sorted (insert x xs)
sorted-insert-sorted x [] p = <> , <>
sorted-insert-sorted x (y :: ys) (y<= , ys-sorted) with total x y
... | left x<=y = (x<=y , all<= x<=y y<=) , y<= , ys-sorted
... | right y<=x = all<=-insert y<=x y<= , sorted-insert-sorted x ys ys-sorted

insert-sort-sorted : ∀(xs : List A) -> sorted (insert-sort xs)
insert-sort-sorted [] = <>
insert-sort-sorted (x :: xs) = sorted-insert-sorted x (insert-sort xs) p
  where
    p = insert-sort-sorted xs

insert-permutation : (x : A) (xs : List A) -> (x :: xs) ## insert x xs
insert-permutation x [] = none
insert-permutation x (y :: ys) with total x y
... | left x<=y = none
... | right y<=x =
  #begin
    (x :: (y :: ys)) ##⟨ just here ⟩
    (y :: (x :: ys)) ##⟨ ##-cong (insert-permutation x ys) ⟩
    (y :: insert x ys)
  #end

insert-sort-permutation : ∀(xs : List A) -> xs ## insert-sort xs
insert-sort-permutation [] = none
insert-sort-permutation (x :: xs) =
  #begin
    (x :: xs)                 ##⟨ ##-cong (insert-sort-permutation xs) ⟩
    (x :: insert-sort xs)     ##⟨ insert-permutation x (insert-sort xs) ⟩
    insert x (insert-sort xs)
  #end


```
