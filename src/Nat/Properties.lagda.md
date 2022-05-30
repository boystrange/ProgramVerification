---
---

```agda
module Nat.Properties where

open import Nat
open import Logic
open import Equality
open import Equality.Reasoning

+-associative : ∀(x y z : ℕ) -> x + (y + z) == (x + y) + z
+-associative zero y z = refl
+-associative (succ x) y z = cong succ (+-associative x y z)

+-zero : ∀(x : ℕ) -> x == x + 0
+-zero zero     = refl
+-zero (succ x) = cong succ (+-zero x)

+-succ : ∀(x y : ℕ) -> succ (x + y) == x + succ y
+-succ zero y = refl
+-succ (succ x) y = cong succ (+-succ x y)

+-commutative : ∀(x y : ℕ) -> x + y == y + x
+-commutative zero y = +-zero y
+-commutative (succ x) y =
  begin
    succ x + y   ==⟨⟩
    succ (x + y) ==⟨ cong succ (+-commutative x y) ⟩
    succ (y + x) ==⟨ +-succ y x ⟩
    y + succ x
  end

_=?_ : (x y : ℕ) -> Decidable (x == y)
zero   =? zero   = yes refl
zero   =? succ y = no λ ()
succ x =? zero   = no (λ ())
succ x =? succ y with x =? y
... | yes eq = yes (cong succ eq)
... | no neq = no λ { refl -> neq refl }

infix 4 _=?_
```
