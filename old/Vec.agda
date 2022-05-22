
open import Type
open import Nat
open import Equality

data Vec (A : Type) : ℕ -> Type where
  []   : Vec A zero
  _::_ : ∀{n : ℕ} -> A -> Vec A n -> Vec A (succ n)

[_] : ∀{A : Type} -> A -> Vec A (succ zero)
[ x ] = x :: []

_++_ : ∀{A : Type} {m n : ℕ} -> Vec A m -> Vec A n -> Vec A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : ∀{A : Type} {n : ℕ} -> Vec A n -> Vec A n
reverse [] = []
reverse {_} {succ n} (x :: xs) rewrite succ-plus-one n = reverse xs ++ [ x ]
