module Exam.Exam1 where

open import Library.Nat
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.List
open import Library.List.Permutation
open import Library.LessThan

data Chop {A : Set} : List A -> List A -> Set where
  chop-last : {x : A} -> Chop (x :: []) []
  chop-next : {x : A} {xs ys : List A} -> Chop xs ys -> Chop (x :: xs) (x :: ys)

chop-test : Chop (0 :: 1 :: 2 :: []) (0 :: 1 :: [])
chop-test = chop-next (chop-next chop-last)

chop-length : {A : Set} {xs ys : List A} -> Chop xs ys -> length xs == succ (length ys)
chop-length chop-last = refl
chop-length (chop-next p) = cong succ (chop-length p)

chop-not-symm : {A : Set} {xs ys : List A} -> Chop xs ys -> ¬ Chop ys xs
chop-not-symm (chop-next p) (chop-next q) = chop-not-symm p q

chop-not-refl : {A : Set} {xs : List A} -> ¬ Chop xs xs
chop-not-refl p = chop-not-symm p p

chop-cong : {A : Set} {xs ys zs : List A} -> Chop xs ys -> Chop (zs ++ xs) (zs ++ ys)
chop-cong {zs = []} p = p
chop-cong {zs = x :: zs} p = chop-next (chop-cong p)
