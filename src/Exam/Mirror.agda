module Exam.Mirror where

open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.List.Properties
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Logic

data Mirror {A : Set} : List A -> Set where
  mirror-0 : Mirror []
  -- mirror-1 : {x : A} -> Mirror [ x ]
  mirror-n : {x : A} {xs : List A} -> Mirror xs -> Mirror ([ x ] ++ xs ++ [ x ])

Palindrome : {A : Set} -> List A -> Set
Palindrome xs = xs == reverse xs

mirror-pal : {A : Set} {xs : List A} -> Mirror xs -> Palindrome xs
mirror-pal mirror-0 = refl
-- mirror-pal mirror-1 = refl
mirror-pal (mirror-n {x} {xs} p) =
  begin
    [ x ] ++ xs ++ [ x ] ==⟨ refl ⟩
    x :: xs ++ [ x ] ==⟨ cong (x ::_) (cong (_++ [ x ]) (mirror-pal p)) ⟩
    x :: reverse xs ++ [ x ] ==⟨ refl ⟩
    reverse [ x ] ++ reverse (x :: xs) ==⟨ symm (reverse-++ (x :: xs) [ x ]) ⟩
    reverse (x :: xs ++ [ x ]) ==⟨ refl ⟩
    reverse ([ x ] ++ xs ++ [ x ])
  end

mirror : {A : Set} (x : A) (xs : List A) -> Mirror (x :: xs) -> ∃[ ys ] xs == ys ++ [ x ]
mirror x [] p = {!!}
mirror x (x₁ :: xs) p = {!!}
