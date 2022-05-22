
open import Type
open import Nat
open import Equality

data List (A : Type) : Type where
  []   : List A
  _::_ : A -> List A -> List A

[_] : ∀{A : Type} -> A -> List A
[ x ] = x :: []

length : ∀{A : Type} -> List A -> ℕ
length [] = zero
length (_ :: xs) = succ (length xs)

_++_ : ∀{A : Type} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

reverse : ∀{A : Type} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

++-length : ∀{A : Type} (xs ys : List A) -> length (xs ++ ys) ≡ length xs + length ys
++-length [] ys = refl
++-length (_ :: xs) ys = context succ (++-length xs ys)

reverse-length : ∀{A : Type} (xs : List A) -> length (reverse xs) ≡ length xs
reverse-length [] = refl
reverse-length (x :: xs) = {!!}
