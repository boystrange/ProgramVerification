module LessThan.Alternative where

open import Nat
open import LessThan

infix 4 _<='_ _<'_

data _<='_ : ℕ -> ℕ -> Set where
  refl : {n : ℕ}   -> n <=' n
  succ : {m n : ℕ} -> m <=' n -> m <=' succ n

_<'_ : ℕ -> ℕ -> Set
x <' y = succ x <=' y

zero<=' : {x : ℕ} -> 0 <=' x
zero<=' {zero}   = refl
zero<=' {succ x} = succ zero<='

succ<=' : {x y : ℕ} -> x <=' y -> succ x <=' succ y
succ<=' refl     = refl
succ<=' (succ p) = succ (succ<=' p)

<=to<=' : {x y : ℕ} -> x <= y -> x <=' y
<=to<=' zero     = zero<='
<=to<=' (succ p) = succ<=' (<=to<=' p)

<='to<= : {x y : ℕ} -> x <=' y -> x <= y
<='to<= refl = le-refl
<='to<= (succ p) = <=-succ (<='to<= p)
