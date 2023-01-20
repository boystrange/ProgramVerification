module Exam.FusionLaw where

open import Library.List
open import Library.Equality
open import Library.Equality.Reasoning

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f a [] = a
foldr f a (x :: xs) = f x (foldr f a xs)

fusion : {A B C : Set} (f : B -> C) (g : A -> B -> B) (a : B) (xs : List A) (h : A -> C -> C) (b : C) ->
         f a == b ->
         ((x : A) (y : B) -> f (g x y) == h x (f y)) ->
         f (foldr g a xs) == foldr h b xs
fusion f g a [] h b p q = p
fusion f g a (x :: xs) h b p q =
  begin
    f (foldr g a (x :: xs)) ==⟨ refl ⟩
    f (g x (foldr g a xs))  ==⟨ q x (foldr g a xs) ⟩
    h x (f (foldr g a xs))  ==⟨ cong (h x) (fusion f g a xs h b p q) ⟩
    h x (foldr h b xs)      ==⟨ refl ⟩
    foldr h b (x :: xs)
  end
