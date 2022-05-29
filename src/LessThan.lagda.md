---
---

```agda
module LessThan where

  open import Nat
  open import Nat.Properties
  open import Logic
  open import Sum
  open import Product
  open import TotalOrder
  open import Equality

  infix 4 _<=_ _>=_ _<_ _>_

  data _<=_ : ℕ -> ℕ -> Set where
    zero : ∀{n : ℕ} -> 0 <= n
    succ : ∀{m n : ℕ} -> m <= n -> succ m <= succ n

  _>=_ : ℕ -> ℕ -> Set
  m >= n = n <= m

  _<_ : ℕ -> ℕ -> Set
  m < n = succ m <= n

  _>_ : ℕ -> ℕ -> Set
  m > n = n < m

  <implies<= : {m n : ℕ} -> m < n -> m <= n
  <implies<= {zero} {_} _ = zero
  <implies<= {succ _} {succ _} (succ p) = succ (<implies<= p)

  <=-succ : ∀{m n : ℕ} -> m <= n -> m <= succ n
  <=-succ zero = zero
  <=-succ (succ p) = succ (<=-succ p)

  <=-succ-succ : {m n : ℕ} -> succ m <= succ n -> m <= n
  <=-succ-succ (succ p) = p

  <=split+ : ∀{x y z : ℕ} -> x + y <= z -> (x <= z) ∧ (y <= z)
  <=split+ {zero} p = zero , p
  <=split+ {succ x} {y} {succ z} (succ p) with <=split+ {x} p
  ... | x<=z , y<=z = succ x<=z , <=-succ y<=z

  <=total : (m n : ℕ) -> m <= n ∨ n <= m
  <=total zero n = left zero
  <=total (succ m) zero = right zero
  <=total (succ m) (succ n) with <=total m n
  ... | left  le = left (succ le)
  ... | right ge = right (succ ge)

  <=antisymm : {m n : ℕ} -> m <= n -> n <= m -> m == n
  <=antisymm zero zero = refl
  <=antisymm (succ le) (succ ge) = cong succ (<=antisymm le ge)

  <=refl : (n : ℕ) -> n <= n
  <=refl zero = zero
  <=refl (succ n) = succ (<=refl n)

  <=trans : {m n o : ℕ} -> m <= n -> n <= o -> m <= o
  <=trans zero q = zero
  <=trans (succ p) (succ q) = succ (<=trans p q)

  data Trichotomy (m n : ℕ) : Set where
    LT : m < n  -> Trichotomy m n
    EQ : m == n -> Trichotomy m n
    GT : m > n  -> Trichotomy m n

  <=trichotomy : (m n : ℕ) -> Trichotomy m n
  <=trichotomy zero zero = EQ refl
  <=trichotomy zero (succ n) = LT (succ zero)
  <=trichotomy (succ m) zero = GT (succ zero)
  <=trichotomy (succ m) (succ n) with <=trichotomy m n
  ... | LT lt   = LT (succ lt)
  ... | EQ refl = EQ refl
  ... | GT gt   = GT (succ gt)

  <=-total-order : TotalOrder ℕ
  TotalOrder._≼_       <=-total-order = _<=_
  TotalOrder.≼total    <=-total-order = <=total
  TotalOrder.≼antisymm <=-total-order = <=antisymm
  TotalOrder.≼refl     <=-total-order = <=refl
  TotalOrder.≼trans    <=-total-order = <=trans

  <=-cong-+ : ∀{x x' y y'} -> x <= x' -> y <= y' -> x + y <= x' + y'
  <=-cong-+ zero zero = zero
  <=-cong-+ {_} {x'} {_} {succ y'} zero (succ q) rewrite symm (+-succ x' y') =
    succ (<=-cong-+ zero q)
  <=-cong-+ (succ p) q = succ (<=-cong-+ p q)

  <=min : ∀{x y z} -> x <= y -> x <= z -> x <= min y z
  <=min zero q = zero
  <=min (succ p) (succ q) = succ (<=min p q)

  <=max : ∀{x y z} -> x <= z -> y <= z -> max x y <= z
  <=max zero q = q
  <=max (succ p) zero = succ p
  <=max (succ p) (succ q) = succ (<=max p q)
```
