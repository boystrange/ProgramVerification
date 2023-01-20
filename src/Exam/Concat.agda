module Exam.Concat where

open import Library.Nat
open import Library.List
open import Library.List.Properties
open import Library.Equality
open import Library.Equality.Reasoning

concat : {A : Set} -> List (List A) -> List A
concat [] = []
concat (xs :: xss) = xs ++ concat xss

sum : List ℕ -> ℕ
sum [] = 0
sum (x :: xs) = x + sum xs

length-concat : {A : Set} (xss : List (List A)) -> length (concat xss) == sum (map length xss)
length-concat [] = refl
length-concat (xs :: xss) =
  begin
    length (concat (xs :: xss))       ==⟨ refl ⟩
    length (xs ++ concat xss)         ==⟨ ++-length xs (concat xss) ⟩
    length xs + length (concat xss)   ==⟨ cong (length xs +_) (length-concat xss) ⟩
    length xs + sum (map length xss)  ==⟨ refl ⟩
    sum (length xs :: map length xss) ==⟨ refl ⟩
    sum (map length (xs :: xss))
  end
