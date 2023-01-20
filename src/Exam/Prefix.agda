module Exam.Prefix where

open import Library.List
open import Library.Equality
open import Library.LessThan
open import Library.Nat

data Prefix {A : Set} : List A -> List A -> Set where
  prefix-[] : {ys : List A} -> Prefix [] ys
  prefix-:: : {x : A} {xs ys : List A} -> Prefix xs ys -> Prefix (x :: xs) (x :: ys)

prefix-refl : {A : Set} (xs : List A) -> Prefix xs xs
prefix-refl [] = prefix-[]
prefix-refl (x :: xs) = prefix-:: (prefix-refl xs)

prefix-trans : {A : Set} {xs ys zs : List A} -> Prefix xs ys -> Prefix ys zs -> Prefix xs zs
prefix-trans prefix-[] q = prefix-[]
prefix-trans (prefix-:: p) (prefix-:: q) = prefix-:: (prefix-trans p q)

prefix-antisymm : {A : Set} {xs ys : List A} -> Prefix xs ys -> Prefix ys xs -> xs == ys
prefix-antisymm prefix-[] prefix-[] = refl
prefix-antisymm (prefix-:: p) (prefix-:: q) = cong (_ ::_) (prefix-antisymm p q)

prefix-length : {A : Set} {xs ys : List A} -> Prefix xs ys -> length xs <= length ys
prefix-length prefix-[] = le-zero
prefix-length (prefix-:: p) = le-succ (prefix-length p)

prefix-map : {A B : Set} {xs ys : List A} {f : A -> B} -> Prefix xs ys -> Prefix (map f xs) (map f ys)
prefix-map prefix-[] = prefix-[]
prefix-map (prefix-:: p) = prefix-:: (prefix-map p)
