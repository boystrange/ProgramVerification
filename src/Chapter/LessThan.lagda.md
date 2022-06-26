---
---

```

open import Bool
open import Nat
open import Logic
open import Equality

module Chapter.LessThan where

-- this is how a programmer would define <=: can decide whether x <=
-- y or not, x <= y is not a type, so we cannot write "give me x and
-- y such that x <= y" but we can write "give me x and y such that x
-- <=₁ y == true"

_<=₁_ : ℕ -> ℕ -> Bool
zero   <=₁ y      = true
succ x <=₁ zero   = false
succ x <=₁ succ y = x <=₁ y

-- can say "give me x and y such that x <=₂ y, which is a type"
-- however, the structure of the proof doesn't say anything about x
-- and y. In fact, any such proof is just <>, we don't know where it
-- comes from

_<=₂_ : ℕ -> ℕ -> Set
zero   <=₂ y      = ⊤
succ x <=₂ zero   = ⊥
succ x <=₂ succ y = x <=₂ y

data _<=₃_ : ℕ -> ℕ -> Set where
  le-zero : {n : ℕ} -> 0 <=₃ n
  le-succ : {m n : ℕ} -> m <=₃ n -> succ m <=₃ succ n

-- this is how a mathematician would define <=

_<=₄_ : ℕ -> ℕ -> Set
x <=₄ y = ∃[ z ] x + z == y

1=>2 : {x y : ℕ} -> x <=₁ y == true -> x <=₂ y
1=>2 {zero}   {y}      eq = <>
1=>2 {succ x} {succ y} eq = 1=>2 {x} {y} eq

2=>3 : {m n : ℕ} -> m <=₂ n -> m <=₃ n
2=>3 {zero}   {n}      le = le-zero
2=>3 {succ m} {succ n} le = le-succ (2=>3 le)

3=>4 : {m n : ℕ} -> m <=₃ n -> m <=₄ n
3=>4 {zero}   {n}      le-zero      = n , refl
3=>4 {succ m} {succ n} (le-succ le) with 3=>4 le
... | z , eq = z , cong succ eq

4=>1 : {m n : ℕ} -> m <=₄ n -> m <=₁ n == true
4=>1 {x} {.(x + z)} (z , refl) = lem x z
  where
    lem : (x z : ℕ) -> (x <=₁ (x + z)) == true
    lem zero     _ = refl
    lem (succ x) z = lem x z

_<=_ : ℕ -> ℕ -> Set
_<=_ = _<=₃_

le-refl : {x : ℕ} -> x <= x
le-refl {zero}   = le-zero
le-refl {succ x} = le-succ le-refl

le-trans : {x y z : ℕ} -> x <= y -> y <= z -> x <= z
le-trans le-zero     q           = le-zero
le-trans (le-succ p) (le-succ q) = le-succ (le-trans p q)

le-total : (x y : ℕ) -> x <= y ∨ y <= x
le-total zero y = inl le-zero
le-total (succ x) zero = inr le-zero
le-total (succ x) (succ y) with le-total x y
... | inl x<=y = inl (le-succ x<=y)
... | inr y<=x = inr (le-succ y<=x)

_<=?_ : (x y : ℕ) -> Decidable (x <= y)
zero <=? y = inr le-zero
succ x <=? zero = inl λ ()
succ x <=? succ y with x <=? y
... | inl gt = inl λ { (le-succ le) -> gt le }
... | inr le = inr (le-succ le)

```
