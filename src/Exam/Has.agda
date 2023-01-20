module Exam.Has where

open import Library.List
open import Library.Logic
open import Library.Equality

-- define a predicate Has x xs that holds if x occurs in xs

data Has {A : Set} : A -> List A -> Set where
  has-here : {x : A} {xs : List A} -> Has x (x :: xs)
  has-next : {x y : A} {xs : List A} -> Has x xs -> Has x (y :: xs)

has : {A : Set} (x : A) (xs : List A) -> Has x xs -> ∃[ ys ] ∃[ zs ] xs == ys ++ x :: zs
has x (.x :: xs) has-here = [] , xs , refl
has x (y :: xs) (has-next p) with has x xs p
... | ys , zs , eq = y :: ys , zs , cong (y ::_) eq
