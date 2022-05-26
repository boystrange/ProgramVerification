---
---

```agda
module TotalOrder where

open import Logic
open import Equality

record TotalOrder {A : Set} : Set₁ where
  field
    _≼_       : A -> A -> Set
    ≼total    : (x y : A) -> x ≼ y ∨ y ≼ x
    ≼antisymm : (x y : A) -> x ≼ y -> y ≼ x -> x == y
    ≼refl     : (x : A) -> x ≼ x
    ≼trans    : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z
```
