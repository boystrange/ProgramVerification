---
---

```agda
module TotalOrder where

open import Sum
open import Equality

record TotalOrder {A : Set} : Set₁ where
  field
    _<=_ : A -> A -> Set
    total : (x y : A) -> (x <= y) ⊎ (y <= x)
    antisymmetry : (x y : A) -> x <= y -> y <= x -> x == y
    reflexivity : (x : A) -> x <= x
    transitivity : (x y z : A) -> x <= y -> y <= z -> x <= z
```
