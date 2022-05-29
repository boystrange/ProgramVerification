---
title: Lists
---

```agda
module List where

open import Nat
open import Logic
open import Product

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

[_] : ∀{A : Set} -> A -> List A
[ x ] = x :: []

_++_ : ∀{A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _::_ _++_

map : ∀{A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

zip : ∀{A B : Set} -> List A -> List B -> List (A × B)
zip [] ys = []
zip (x :: xs) [] = []
zip (x :: xs) (y :: ys) = (x , y) :: zip xs ys

unzip : {A B : Set} -> List (A × B) -> List A × List B
unzip [] = [] , []
unzip ((x , y) :: xs) with unzip xs
... | xs , ys = x :: xs , y :: ys

reverse : ∀{A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-onto : ∀{A : Set} -> List A -> List A -> List A
reverse-onto []        ys = ys
reverse-onto (x :: xs) ys = reverse-onto xs (x :: ys)

fast-reverse : ∀{A : Set} -> List A -> List A
fast-reverse xs = reverse-onto xs []

length : ∀{A : Set} -> List A -> ℕ
length []        = 0
length (_ :: xs) = succ (length xs)

all : {A : Set} -> (A -> Set) -> List A -> Set
all P [] = ⊤
all P (x :: xs) = P x ∧ all P xs

foldl : {A B : Set} -> (A -> B -> A) -> A -> List B -> A
foldl f a [] = a
foldl f a (x :: xs) = foldl f (f a x) xs

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f a [] = a
foldr f a (x :: xs) = f x (foldr f a xs)
```
