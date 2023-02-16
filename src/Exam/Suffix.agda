module Exam.Suffix where

open import Library.List
open import Library.Equality
open import Library.LessThan
open import Library.Nat
open import Library.Logic

data Suffix {A : Set} (xs : List A) : List A -> Set where
  srefl : Suffix xs xs
  snext : {x : A} {ys : List A} -> Suffix xs ys -> Suffix xs (x :: ys)

suffix-refl : {A : Set} (xs : List A) -> Suffix xs xs
suffix-refl _ = srefl

suffix-:: : {A : Set} {x : A} {xs ys : List A} -> Suffix (x :: xs) ys -> Suffix xs ys
suffix-:: srefl = snext srefl
suffix-:: (snext p) = snext (suffix-:: p)

suffix-trans : {A : Set} {xs ys zs : List A} -> Suffix xs ys -> Suffix ys zs -> Suffix xs zs
suffix-trans srefl q = q
suffix-trans (snext p) q = suffix-trans p (suffix-:: q)

suffix-length : {A : Set} {xs ys : List A} -> Suffix xs ys -> length xs <= length ys
suffix-length srefl = le-refl
suffix-length (snext p) = le-succ-r (suffix-length p)

suffix-++ : {A : Set} {xs ys : List A} -> Suffix xs ys -> ∃[ zs ] ys == zs ++ xs
suffix-++ srefl = [] , refl
suffix-++ (snext {x} p) with suffix-++ p
... | zs , refl = x :: zs , cong (x ::_) refl
