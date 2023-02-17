module Exam.LinearSearch where

open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Equality
open import Library.Logic
open import Library.Logic.Laws
open import Library.LessThan

_=?_ : (x y : ℕ) -> (x == y) ∨ (x != y)
zero =? zero = inl refl
zero =? succ y = inr (λ ())
succ x =? zero = inr (λ ())
succ x =? succ y with x =? y
... | inl p = inl (cong succ p)
... | inr p = inr λ { refl → p refl }

linear-search : ℕ -> List ℕ -> Bool
linear-search x [] = false
linear-search x (y :: xs) with x =? y
... | inl refl = true
... | inr p = linear-search x xs

data _∈_ {A : Set} : A -> List A -> Set where
  ∈-here : (x : A) (xs : List A) -> x ∈ (x :: xs)
  ∈-next : {x y : A} {xs : List A} -> x ∈ xs -> x ∈ (y :: xs)

linear-search-∈ : (x : ℕ) (xs : List ℕ) -> linear-search x xs == true -> x ∈ xs
linear-search-∈ x (y :: xs) eq with x =? y
... | inl refl = ∈-here x xs
... | inr p = ∈-next (linear-search-∈ x xs eq)

∈-linear-search : {x : ℕ} {xs : List ℕ} -> x ∈ xs -> linear-search x xs == true
∈-linear-search (∈-here x xs) with x =? x
... | inl refl = refl
... | inr p = ex-falso (p refl)
∈-linear-search (∈-next {x} {y} p) with x =? y
... | inl refl = refl
... | inr _ = ∈-linear-search p

lemma : (x y : ℕ) (xs : List ℕ) -> ¬ (x ∈ (y :: xs)) -> ¬ (x ∈ xs)
lemma x y xs np p with x =? y
... | inl refl = np (∈-here x xs)
... | inr ne = np (∈-next p)

∉-linear-search : {x : ℕ} {xs : List ℕ} -> ¬ (x ∈ xs) -> linear-search x xs == false
∉-linear-search {x} {[]} p = refl
∉-linear-search {x} {y :: xs} p with x =? y
... | inl refl = ex-falso (p (∈-here x xs))
... | inr ne = ∉-linear-search (lemma x y xs p)

empty : {A : Set} (xs : List A) -> ((y : A) -> ¬ (y ∈ xs)) -> xs == []
empty [] p = refl
empty (x :: xs) p = ex-falso (p x (∈-here x xs))
