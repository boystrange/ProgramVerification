module Exam.Map where

open import Library.List
open import Library.List.Properties
open import Library.Equality
open import Library.Equality.Reasoning

-- f x == f (f x) => map f xs == map f (map f xs)

idem : {A : Set} {f : A -> A} -> ((x : A) -> f x == f (f x)) ->
       (xs : List A) -> map f xs == map f (map f xs)
idem p [] = refl
idem p (x :: xs) = cong2 _::_ (p x) (idem p xs)

map-++ : {A B : Set} {f : A -> B} (xs ys : List A) -> map f (xs ++ ys) == map f xs ++ map f ys
map-++ [] ys = refl
map-++ {_} {_} {f} (x :: xs) ys = cong (f x ::_) (map-++ xs ys)

map-reverse : {A B : Set} {f : A -> B} -> (xs : List A) -> map f (reverse xs) == reverse (map f xs)
map-reverse [] = refl
map-reverse {_} {_} {f} (x :: xs) =
  begin
    map f (reverse (x :: xs)) ==⟨ refl ⟩
    map f (reverse xs ++ [ x ]) ==⟨ map-++ (reverse xs) [ x ] ⟩
    map f (reverse xs) ++ map f [ x ] ==⟨ refl ⟩
    map f (reverse xs) ++ [ f x ] ==⟨ cong (_++ [ f x ]) (map-reverse xs) ⟩
    reverse (map f xs) ++ [ f x ] ==⟨ refl ⟩
    reverse (f x :: map f xs) ==⟨ refl ⟩
    reverse (map f (x :: xs))
  end
