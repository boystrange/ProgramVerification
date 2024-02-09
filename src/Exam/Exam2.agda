module Exam.Exam2 where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.List
open import Library.List.Permutation
open import Library.LessThan

data Merge {A : Set} : List A -> List A -> List A -> Set where
  merge-[] : Merge [] [] []
  merge-l  : {x : A} {xs ys zs : List A} -> Merge xs ys zs ->
             Merge (x :: xs) ys (x :: zs)
  merge-r  : {y : A} {xs ys zs : List A} -> Merge xs ys zs ->
             Merge xs (y :: ys) (y :: zs)

test : Merge (1 :: 3 :: 5 :: []) (0 :: 2 :: []) (0 :: 1 :: 2 :: 3 :: 5 :: [])
test = merge-r (merge-l (merge-r (merge-l (merge-l merge-[]))))

merge-nil : {A : Set} {xs ys : List A} -> Merge xs ys [] -> xs == [] ∧ ys == []
merge-nil merge-[] = refl , refl

merge-sing : {A : Set} {x : A} {xs ys : List A} -> Merge xs ys [ x ] -> xs == [] ∨ ys == []
merge-sing (merge-l p) with merge-nil p
... | _ , eq = inr eq
merge-sing (merge-r p) with merge-nil p
... | eq , _ = inl eq

merge-symm : {A : Set} {xs ys zs : List A} -> Merge xs ys zs -> Merge ys xs zs
merge-symm merge-[] = merge-[]
merge-symm (merge-l p) = merge-r (merge-symm p)
merge-symm (merge-r p) = merge-l (merge-symm p)

merge-length : {A : Set} {xs ys zs : List A} -> Merge xs ys zs ->
               length zs == length xs + length ys
merge-length merge-[] = refl
merge-length (merge-l p) = cong succ (merge-length p)
merge-length {_} {xs} {y :: ys} {y :: zs} (merge-r p) =
  begin
    length (y :: zs) ==⟨ refl ⟩
    succ (length zs) ==⟨ cong succ (merge-length p) ⟩
    succ (length xs + length ys) ==⟨ +-succ (length xs) (length ys) ⟩
    length xs + succ (length ys) ==⟨ refl ⟩
    length xs + length (y :: ys)
  end

#merge : {A : Set} {xs ys zs : List A} -> Merge xs ys zs -> zs # xs ++ ys
#merge merge-[] = #refl
#merge (merge-l p) = #cong (#merge p)
#merge {_} {xs} {y :: ys} {y :: zs} (merge-r p) =
  #begin
    y :: zs         #⟨ #cong (#merge p) ⟩
    y :: (xs ++ ys) #⟨ #push ⟩
    xs ++ y :: ys
  #end

