---
title: Natural Numbers
---

```agda
module Nat where

  data ℕ : Set where
    zero : ℕ
    succ : ℕ -> ℕ

  {-# BUILTIN NATURAL ℕ #-}

  infixl 6 _+_ _-_
  infixl 7 _*_
  infixl 8 _^_

  _+_ : ℕ -> ℕ -> ℕ
  zero   + y = y
  succ x + y = succ (x + y)

  _-_ : ℕ -> ℕ -> ℕ
  zero   - _      = 0
  succ x - zero   = succ x
  succ x - succ y = x - y

  _*_ : ℕ -> ℕ -> ℕ
  zero   * _ = 0
  succ x * y = y + (x * y)

  _^_ : ℕ -> ℕ -> ℕ
  x ^ zero = 1
  x ^ succ n = x * x ^ n

  min : ℕ -> ℕ -> ℕ
  min zero y = zero
  min (succ x) zero = zero
  min (succ x) (succ y) = succ (min x y)

  max : ℕ -> ℕ -> ℕ
  max zero y = y
  max (succ x) zero = succ x
  max (succ x) (succ y) = succ (max x y)

  _! : ℕ -> ℕ
  zero   ! = 1
  succ n ! = n * (n !)

  module Properties where

    open import Equality

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
```
