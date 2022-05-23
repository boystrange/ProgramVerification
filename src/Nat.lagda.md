---
title: Natural Numbers
---

```agda
module Nat where

open import Equality

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℕ -> ℕ -> ℕ
zero   + y = y
succ x + y = succ (x + y)

_-_ : ℕ -> ℕ -> ℕ
x      - zero     = x
zero   - succ _   = 0
succ x - succ y = x - y

_*_ : ℕ -> ℕ -> ℕ
zero   * _ = 0
succ x * y = y + (x * y)

_! : ℕ -> ℕ
zero   ! = 1
succ n ! = n * (n !)

+-associative : ∀(x y z : ℕ) -> x + (y + z) == (x + y) + z
+-associative zero y z = refl
+-associative (succ x) y z = cong succ (+-associative x y z)

+-zero : ∀(x : ℕ) -> x == x + 0
+-zero zero     = refl
+-zero (succ x) = cong succ (+-zero x)

+-succ : ∀(x y : ℕ) -> succ (x + y) == x + succ y
+-succ zero y = refl
+-succ (succ x) y = cong succ (+-succ x y)

-- lemma+succ : ∀(x y : ℕ) -> succ x + y == x + succ y
-- lemma+succ zero y = refl
-- lemma+succ (succ x) y = context succ (lemma+succ x y)

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
