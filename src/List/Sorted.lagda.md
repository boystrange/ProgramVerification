---
---

```agda
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

  sorted : List A -> Set
  sorted [] = ⊤
  sorted (x :: xs) = x ≼* xs ∧ sorted xs
```
