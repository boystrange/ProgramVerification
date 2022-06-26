---
---

```agda
open import Logic
open import List
open import List.Properties
open import List.Permutation

module Chapter.ExtrinsicInsertionSort
  (A : Set)
  (_≼_ : A -> A -> Set)
  (≼-trans : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z)
  (≼-total : (x y : A) -> x ≼ y ∨ y ≼ x)
  where

open import List.Sorted A _≼_

insert : A -> List A -> List A
insert x [] = x :: []
insert x (y :: ys) with ≼-total x y
... | inl x≼y = x :: y :: ys
... | inr y≼x = y :: insert x ys

insert-sort : List A -> List A
insert-sort [] = []
insert-sort (x :: xs) = insert x (insert-sort xs)

all-insert : {x : A} {xs : List A} {P : A -> Set} -> P x -> All P xs -> All P (insert x xs)
all-insert {x} {[]} p <> = p , <>
all-insert {x} {y :: _} p (q , ps) with ≼-total x y
... | inl x≼y = p , q , ps
... | inr y≼x = q , all-insert p ps

sorted-insert-sorted : (x : A) (xs : List A) -> Sorted xs -> Sorted (insert x xs)
sorted-insert-sorted x [] ps = <> , <>
sorted-insert-sorted x (y :: xs) (p , ps) with ≼-total x y
... | inl x≼y = (x≼y , implies-all (≼-trans x≼y) p) , p , ps
... | inr y≼x = all-insert y≼x p , sorted-insert-sorted x xs ps

insert-sort-sorted : (xs : List A) -> Sorted (insert-sort xs)
insert-sort-sorted [] = <>
insert-sort-sorted (x :: xs) = sorted-insert-sorted x (insert-sort xs) (insert-sort-sorted xs)

insert-permutation : (x : A) (xs : List A) -> x :: xs # insert x xs
insert-permutation x [] = #refl
insert-permutation x (y :: ys) with ≼-total x y
... | inl x≼y = #refl
... | inr y≼x =
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
```
