---
---

```agda
open import Fun using (_∘_)
open import Nat
open import Fin
open import Equality

data Vec (A : Set) : ℕ -> Set where
  []   : Vec A zero
  _::_ : ∀{n : ℕ} -> A -> Vec A n -> Vec A (succ n)

vector : ∀{A : Set} {n : ℕ} -> A -> Vec A n
vector {_} {zero} _ = []
vector {_} {succ n} x = x :: vector x

_++_ : ∀{A : Set} {m n : ℕ} -> Vec A m -> Vec A n -> Vec A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_!!_ : ∀{A : Set} {n : ℕ} -> Vec A n -> Fin n -> A
(x :: _)  !! zero   = x
(_ :: xs) !! succ i = xs !! i

head : ∀{A : Set} {n : ℕ} -> Vec A (succ n) -> A
head = _!! zero

tail : ∀{A : Set} {n : ℕ} -> Vec A (succ n) -> Vec A n
tail (_ :: xs) = xs

map : ∀{A B : Set} {n : ℕ} -> (A -> B) -> Vec A n -> Vec B n
map f []        = []
map f (x :: xs) = f x :: map f xs

zip-with : ∀{A B C : Set} {n : ℕ} -> (A -> B -> C) -> Vec A n -> Vec B n -> Vec C n
zip-with f []        []        = []
zip-with f (x :: xs) (y :: ys) = f x y :: zip-with f xs ys

foldr : ∀{A B : Set}{n : ℕ} -> (A -> B -> B) -> B -> Vec A n -> B
foldr f y [] = y
foldr f y (x :: xs) = f x (foldr f y xs)

-- TODO: infix ++ e !!
```
