module Exam.Unzip where

open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.Logic
open import Library.List.Permutation
open import Library.Equality
open import Library.Equality.Reasoning

unzip : {A : Set} -> List A -> (List A ∧ List A)
unzip [] = [] , []
unzip (x :: []) = [ x ] , []
unzip (x :: y :: xs) with unzip xs
... | ys , zs = x :: ys , y :: zs

uncurry : {A B C : Set} -> (A -> B -> C) -> A ∧ B -> C
uncurry f (x , y) = f x y

data Unzip {A : Set} : List A -> List A -> List A -> Set where
  unzip-0 : Unzip [] [] []
  unzip-1 : (x : A) -> Unzip [ x ] [ x ] []
  unzip-n : (y z : A) (xs ys zs : List A) -> Unzip xs ys zs -> Unzip (y :: z :: xs) (y :: ys) (z :: zs)

unzip-length : {A : Set} {xs ys zs : List A} -> Unzip xs ys zs -> length xs == length ys + length zs
unzip-length unzip-0 = refl
unzip-length (unzip-1 x) = refl
unzip-length (unzip-n y z xs ys zs p) =
  begin
    length (y :: z :: xs) ==⟨ refl ⟩
    succ (succ (length xs)) ==⟨ cong succ (cong succ (unzip-length p)) ⟩
    succ (succ (length ys + length zs)) ==⟨ refl ⟩
    succ (succ (length ys) + length zs) ==⟨ refl ⟩
    succ (length (y :: ys) + length zs) ==⟨ +-succ (succ (length ys)) (length zs) ⟩
    length (y :: ys) + succ (length zs) ==⟨ refl ⟩
    length (y :: ys) + length (z :: zs)
  end

unzip-permutation : {A : Set} {xs ys zs : List A} -> Unzip xs ys zs -> xs # (ys ++ zs)
unzip-permutation unzip-0 = #refl
unzip-permutation (unzip-1 x) = #refl
unzip-permutation (unzip-n y z xs ys zs p) with unzip-permutation p
... | π = #cong (#trans (#cong π) #push)
