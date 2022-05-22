
open import Type
open import Equality

data ℕ : Type where
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
+-associative (succ x) y z = context succ (+-associative x y z)

lemma+0 : ∀(x : ℕ) -> x == x + 0
lemma+0 zero     = refl
lemma+0 (succ x) = context succ (lemma+0 x)

lemma+1 : ∀(x : ℕ) -> succ x == x + 1
lemma+1 zero     = refl
lemma+1 (succ x) = context succ (lemma+1 x)

lemma+succ : ∀(x y : ℕ) -> succ x + y == x + succ y
lemma+succ zero y = refl
lemma+succ (succ x) y = context succ (lemma+succ x y)

+-commutative : ∀(x y : ℕ) -> x + y == y + x
+-commutative zero y = lemma+0 y
+-commutative (succ x) y = ==-transitive (context succ (+-commutative x y)) (lemma+succ y x)
