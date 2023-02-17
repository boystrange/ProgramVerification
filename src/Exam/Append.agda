module Exam.Append where

open import Library.List
open import Library.Equality

data Append {A : Set} : List A -> List A -> List A -> Set where
  app-[] : (xs : List A) -> Append [] xs xs
  app-:: : (x : A) {xs ys zs : List A} -> Append xs ys zs -> Append (x :: xs) ys (x :: zs)

append-++ : {A : Set} {xs ys zs : List A} -> Append xs ys zs -> xs ++ ys == zs
append-++ (app-[] _) = refl
append-++ (app-:: x p) = cong (x ::_) (append-++ p)

++-append : {A : Set} (xs ys : List A) -> Append xs ys (xs ++ ys)
++-append [] ys = app-[] ys
++-append (x :: xs) ys = app-:: x (++-append xs ys)

append-injective : {A : Set} {xs ys us vs : List A} -> Append xs ys us -> Append xs ys vs -> us == vs
append-injective (app-[] _) (app-[] _) = refl
append-injective (app-:: x p) (app-:: .x q) = cong (x ::_) (append-injective p q)
