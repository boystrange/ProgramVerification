---
---

```agda
module QuickSort where

open import Nat
open import Product
open import Sum
open import Equality
open import List
open import LessThan
open import Permutation
open import Logic
open import Bool

variable A : Set

data Ordering {A : Set} (R : A -> A -> Set) : A -> A -> Set where
  EQ : ∀{x : A} -> Ordering R x x
  LT : ∀{x y : A} -> R x y -> Ordering R x y
  GT : ∀{x y : A} -> R y x -> Ordering R x y

-- guardare lezioni su overloading di Peter Selinger
postulate
  _≼_ : A -> A -> Set
  total : (x y : A) -> (x ≼ y) ∨ (y ≼ x)
  reflexive : (x : A) -> x ≼ x
  antisymmetric : (x y : A) -> x ≼ y -> y ≼ x -> x == y
  transitive : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z

partition : ∀{A : Set} -> A -> List A -> List A × List A
partition x [] = [] , []
partition x (y :: xs) with total x y
... | left x≼y = let ys , zs = partition x xs in y :: ys , zs
... | right y≼x = let ys , zs = partition x xs in ys , y :: zs

-- quick-sort : ∀{A : Set} -> List A -> List A
-- quick-sort [] = []
-- quick-sort (x :: xs) =
--   let ys , zs = partition x xs in
--   quick-sort ys ++ (x :: quick-sort zs)

partition<= : ∀{A : Set} (x : A) (xs : List A) (n : ℕ) -> length xs <= n ->
  let ys , zs = partition x xs in
  length ys <= n × length zs <= n
partition<= x [] n p = zero , zero
partition<= x (y :: xs) (succ n) (succ p) with total x y
... | left x≼y = let p1 , p2 = partition<= x xs n p in succ p1 , <=-succ p2
... | right y≼x = let p1 , p2 = partition<= x xs n p in <=-succ p1 , succ p2

partition-permutation : ∀{A : Set} (x : A) (xs : List A) (n : ℕ) -> length xs <= n ->
  let ys , zs = partition x xs in
  (x :: xs) ## (ys ++ (x :: zs))
partition-permutation x [] n px = none
partition-permutation x (y :: xs) (succ n) (succ p) with total x y
... | left x≼y =
  #begin
    (x :: (y :: xs)) ##⟨ here ⟩
    (y :: (x :: xs)) ##⟨ next (partition-permutation x xs n p) ⟩
    _
  #end
... | right y≼x =
  let ys , zs = partition x xs in
  #begin
    (x :: (y :: xs)) ##⟨ here ⟩
    (y :: (x :: xs)) ##⟨ next (partition-permutation x xs n p) ⟩
    (y :: (ys ++ (x :: zs))) ##⟨ ##-push ⟩
    (ys ++ (y :: (x :: zs))) ##⟨ ##-cong-l here ⟩
    (ys ++ (x :: (y :: zs)))
  #end

quick-sort : ∀{A : Set} (n : ℕ) (xs : List A) -> length xs <= n -> List A
quick-sort _ [] _ = []
quick-sort (succ n) (x :: xs) (succ p) =
  let ys , zs = partition x xs in
  let py , pz = partition<= x xs n p in
  quick-sort n ys py ++ (x :: quick-sort n zs pz)

quick-sort-permutation : ∀{A : Set} (n : ℕ) (xs : List A) (p : length xs <= n) -> xs ## quick-sort n xs p
quick-sort-permutation n [] p = none
quick-sort-permutation (succ n) (x :: xs) (succ p) =
  let ys , zs = partition x xs in
  let py , pz = partition<= x xs n p in
  let indy = quick-sort-permutation n ys py in
  let indz = quick-sort-permutation n zs pz in
  #begin
    (x :: xs)         ##⟨ partition-permutation x xs n p ⟩
    (ys ++ (x :: zs)) ##⟨ ##-cong-l (next indz) ⟩
    (ys ++ (x :: quick-sort n zs pz)) ##⟨ ##-cong-r indy ⟩
    (quick-sort n ys py ++ (x :: quick-sort n zs pz))
  #end
```
