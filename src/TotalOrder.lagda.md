---
---

```agda
module TotalOrder (A : Set) (_≼_ : A -> A -> Set) where

open import Logic
open import Equality

postulate
  ≼total    : (x y : A) -> x ≼ y ∨ y ≼ x
  ≼antisymm : {x y : A} -> x ≼ y -> y ≼ x -> x == y
  ≼refl     : {x : A} -> x ≼ x
  ≼trans    : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z
```
