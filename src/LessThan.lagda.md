---
---

```agda
module LessThan where

open import Nat
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

<=-succ : ∀{m n : ℕ} -> m <= n -> m <= succ n
<=-succ zero = zero
<=-succ (succ p) = succ (<=-succ p)

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

<=trichotomy : (m n : ℕ) -> m < n ∨ m == n ∨ m > n
<=trichotomy zero zero = right (left refl)
<=trichotomy zero (succ n) = left (succ zero)
<=trichotomy (succ m) zero = right (right (succ zero))
<=trichotomy (succ m) (succ n) with <=trichotomy m n
... | left lt = left (succ lt)
... | right (left eq) = right (left (cong succ eq))
... | right (right gt) = right (right (succ gt))

<=-total-order : TotalOrder ℕ
TotalOrder._≼_       <=-total-order = _<=_
TotalOrder.≼total    <=-total-order = <=total
TotalOrder.≼antisymm <=-total-order = <=antisymm
TotalOrder.≼refl     <=-total-order = <=refl
TotalOrder.≼trans    <=-total-order = <=trans

```
