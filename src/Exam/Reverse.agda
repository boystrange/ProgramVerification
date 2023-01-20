module Exam.Reverse where

open import Library.List
open import Library.List.Properties
open import Library.Equality
open import Library.Equality.Reasoning

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

foldl : {A B : Set} -> (B -> A -> B) -> B -> List A -> B
foldl f a [] = a
foldl f a (x :: xs) = foldl f (f a x) xs

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f a [] = a
foldr f a (x :: xs) = f x (foldr f a xs)

foldl-reverse : {A : Set} (xs : List A) -> foldl (flip _::_) [] xs == reverse xs
foldl-reverse xs =
  begin
    foldl (flip _::_) [] xs ==⟨ lemma xs [] ⟩
    reverse xs ++ []        ==⟨ ++-unit-r (reverse xs) ⟩
    reverse xs
  end
  where
    lemma : {A : Set} (xs ys : List A) -> foldl (flip _::_) ys xs == reverse xs ++ ys
    lemma [] ys = refl
    lemma (x :: xs) ys =
      begin
        foldl (flip _::_) ys (x :: xs) ==⟨ refl ⟩
        foldl (flip _::_) (flip _::_ ys x) xs ==⟨ refl ⟩
        foldl (flip _::_) (x :: ys) xs ==⟨ lemma xs (x :: ys) ⟩
        reverse xs ++ (x :: ys) ==⟨ refl ⟩
        reverse xs ++ ([ x ] ++ ys) ==⟨ ++-assoc (reverse xs) [ x ] ys ⟩
        (reverse xs ++ [ x ]) ++ ys ==⟨ refl ⟩
        reverse (x :: xs) ++ ys
      end
