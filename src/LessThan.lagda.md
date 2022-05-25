---
---

```agda
module LessThan where

open import Nat

data _<=_ : ℕ -> ℕ -> Set where
  zero : ∀{n : ℕ} -> 0 <= n
  succ : ∀{m n : ℕ} -> m <= n -> succ m <= succ n

<=-succ : ∀{m n : ℕ} -> m <= n -> m <= succ n
<=-succ zero = zero
<=-succ (succ p) = succ (<=-succ p)
```
