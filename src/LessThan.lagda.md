---
---

```agda
module LessThan where

open import Nat
open import Logic
open import Product

infix 4 _<=_

data _<=_ : ℕ -> ℕ -> Set where
  zero : ∀{n : ℕ} -> 0 <= n
  succ : ∀{m n : ℕ} -> m <= n -> succ m <= succ n

<=-succ : ∀{m n : ℕ} -> m <= n -> m <= succ n
<=-succ zero = zero
<=-succ (succ p) = succ (<=-succ p)

<=split+ : ∀{x y z : ℕ} -> x + y <= z -> (x <= z) ∧ (y <= z)
<=split+ {zero} p = zero , p
<=split+ {succ x} {y} {succ z} (succ p) with <=split+ {x} p
... | x<=z , y<=z = succ x<=z , <=-succ y<=z
```
