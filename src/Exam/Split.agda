module Exam.Split where

open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.Logic
open import Library.List.Permutation
open import Library.Equality
open import Library.Equality.Reasoning

data Split {A : Set} : List A -> List A -> List A -> Set where
  split-[] : Split [] [] []
  split-l : {x : A} {xs ys zs : List A} -> Split xs ys zs -> Split (x :: xs) (x :: ys) zs
  split-r : {x : A} {xs ys zs : List A} -> Split xs ys zs -> Split (x :: xs) ys (x :: zs)

data _∈_ {A : Set} : A -> List A -> Set where
  ∈-here : (x : A) (xs : List A) -> x ∈ (x :: xs)
  ∈-next : {x y : A} {xs : List A} -> x ∈ xs -> x ∈ (y :: xs)

split-permutation : {A : Set} {xs ys zs : List A} -> Split xs ys zs -> xs # ys ++ zs
split-permutation split-[] = #refl
split-permutation (split-l p) = #cong (split-permutation p)
split-permutation (split-r p) = #trans (#cong (split-permutation p)) #push

split-length : {A : Set} {xs ys zs : List A} -> Split xs ys zs -> length xs == length ys + length zs
split-length split-[] = refl
split-length (split-l p) = cong succ (split-length p)
split-length (split-r {x} {xs} {ys} {zs} p) =
  begin
    length (x :: xs) ==⟨ refl ⟩
    succ (length xs) ==⟨ cong succ (split-length p) ⟩
    succ (length ys + length zs) ==⟨ +-succ (length ys) (length zs) ⟩
    length ys + succ (length zs) ==⟨ refl ⟩
    length ys + length (x :: zs)
  end

split-∈ : {A : Set} {x : A} {xs ys zs : List A} -> Split xs ys zs -> x ∈ xs -> x ∈ ys ∨ x ∈ zs
split-∈ (split-l p) (∈-here x xs) = inl (∈-here x _)
split-∈ (split-r p) (∈-here x xs) = inr (∈-here x _)
split-∈ (split-l p) (∈-next q) with split-∈ p q
... | inl r = inl (∈-next r)
... | inr r = inr r
split-∈ (split-r p) (∈-next q) with split-∈ p q
... | inl r = inl r
... | inr r = inr (∈-next r)

sum : List ℕ -> ℕ
sum [] = 0
sum (x :: xs) = x + sum xs

split-comm : {A : Set} {xs ys zs : List A} -> Split xs ys zs -> Split xs zs ys
split-comm split-[] = split-[]
split-comm (split-l p) = split-r (split-comm p)
split-comm (split-r p) = split-l (split-comm p)

split-refl : {A : Set} (xs : List A) -> Split xs [] xs
split-refl [] = split-[]
split-refl (x :: xs) = split-r (split-refl xs)

split-++ : {A : Set} (xs ys : List A) -> Split (xs ++ ys) xs ys
split-++ [] ys = split-refl ys
split-++ (x :: xs) ys = split-l (split-++ xs ys)

split-sum : {xs ys zs : List ℕ} -> Split xs ys zs -> sum xs == sum ys + sum zs
split-sum split-[] = refl
split-sum (split-l {x} {xs} {ys} {zs} p) =
  begin
    sum (x :: xs) ==⟨ refl ⟩
    x + sum xs ==⟨ cong (x +_) (split-sum p) ⟩
    x + (sum ys + sum zs) ==⟨ +-assoc x (sum ys) (sum zs) ⟩
    (x + sum ys) + sum zs ==⟨ refl ⟩
    sum (x :: ys) + sum zs
  end
split-sum (split-r {x} {xs} {ys} {zs} p) =
  begin
    sum (x :: xs) ==⟨ refl ⟩
    x + sum xs ==⟨ cong (x +_) (split-sum p) ⟩
    x + (sum ys + sum zs) ==⟨ +-assoc x (sum ys) (sum zs) ⟩
    (x + sum ys) + sum zs ==⟨ cong (_+ sum zs) (+-comm x (sum ys)) ⟩
    (sum ys + x) + sum zs ==⟨ symm (+-assoc (sum ys) x (sum zs)) ⟩
    sum ys + (x + sum zs) ==⟨ refl ⟩
    sum ys + sum (x :: zs)
  end
