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
  zero : {x : ℕ}   -> 0 <= x
  succ : {x y : ℕ} -> x <= y -> succ x <= succ y

_>=_ : ℕ -> ℕ -> Set
x >= y = y <= x

_<_ : ℕ -> ℕ -> Set
x < y = succ x <= y

_>_ : ℕ -> ℕ -> Set
x > y = y < x

<=-succ : ∀{m n : ℕ} -> m <= n -> m <= succ n
<=-succ zero = zero
<=-succ (succ p) = succ (<=-succ p)

not-lt-ge : {x y : ℕ} -> ¬ (x < y) -> (y <= x)
not-lt-ge {_}      {zero}   p = zero
not-lt-ge {zero}   {succ _} p = absurd (p (succ zero))
not-lt-ge {succ _} {succ _} p = succ (not-lt-ge λ q -> p (succ q))

<=split+ : {x y z : ℕ} -> (x + y <= z) -> (x <= z) ∧ (y <= z)
<=split+ {zero} p = zero , p
<=split+ {succ x} {y} {succ z} (succ p) with <=split+ {x} p
... | x<=z , y<=z = succ x<=z , <=-succ y<=z

le-total : (m n : ℕ) -> m <= n ∨ n <= m
le-total zero n = left zero
le-total (succ m) zero = right zero
le-total (succ m) (succ n) with le-total m n
... | left  le = left (succ le)
... | right ge = right (succ ge)

le-antisymm : {m n : ℕ} -> m <= n -> n <= m -> m == n
le-antisymm zero     zero     = refl
le-antisymm (succ p) (succ q) = cong succ (le-antisymm p q)

le-refl : {n : ℕ} -> n <= n
le-refl {zero}   = zero
le-refl {succ n} = succ le-refl

le-trans : {m n o : ℕ} -> m <= n -> n <= o -> m <= o
le-trans zero     _        = zero
le-trans (succ p) (succ q) = succ (le-trans p q)

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

le-total-order : TotalOrder ℕ
TotalOrder._≼_       le-total-order = _<=_
TotalOrder.≼total    le-total-order = le-total
TotalOrder.≼antisymm le-total-order = le-antisymm
TotalOrder.≼refl     le-total-order = le-refl
TotalOrder.≼trans    le-total-order = le-trans

<=-cong-+ : ∀{x x' y y'} -> x <= x' -> y <= y' -> x + y <= x' + y'
<=-cong-+ zero zero = zero
<=-cong-+ {_} {x'} {_} {succ y'} zero (succ q) rewrite symm (+-succ x' y') =
  succ (<=-cong-+ zero q)
<=-cong-+ (succ p) q = succ (<=-cong-+ p q)

le-min : ∀{x y z} -> x <= y -> x <= z -> x <= min y z
le-min zero q = zero
le-min (succ p) (succ q) = succ (le-min p q)

le-max : ∀{x y z} -> x <= z -> y <= z -> max x y <= z
le-max zero q = q
le-max (succ p) zero = succ p
le-max (succ p) (succ q) = succ (le-max p q)

_<=?_ : (x y : ℕ) -> Decidable (x <= y)
zero <=? y = yes zero
succ x <=? zero = no (λ ())
succ x <=? succ y with x <=? y
... | yes le = yes (succ le)
... | no nle = no λ { (succ p) -> nle p }

_<?_ : (x y : ℕ) -> Decidable (x < y)
x <? y = succ x <=? y
