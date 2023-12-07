module Exam.BelongsExamSolutions where

open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.List
open import Library.List.Permutation
open import Library.LessThan

infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A -> Set where
  in-head : {xs : List A} -> x ∈ (x :: xs)
  in-tail : {y : A} {xs : List A} -> x ∈ xs -> x ∈ (y :: xs)

-- EX1

_ : 2 ∈ (0 :: 1 :: 2 :: 3 :: 4 :: [])
_ = in-tail (in-tail in-head)

ex2 : ∀{A : Set} {x : A} (xs ys : List A) -> x ∈ xs ++ x :: ys
ex2 [] ys = in-head
ex2 (_ :: xs) ys = in-tail (ex2 xs ys)

ex3 : ∀{A : Set} {x : A} {xs : List A} -> x ∈ xs -> 1 <= length xs
ex3 in-head = le-succ le-zero
ex3 (in-tail p) = le-succ le-zero

ex4 : ∀{A : Set} (xs : List A) -> (∀(x : A) -> ¬ (x ∈ xs)) -> xs == []
ex4 [] p = refl
ex4 (x :: xs) p = ex-falso (p x in-head)

ex5 : ∀{A : Set} {x : A} {xs ys : List A} -> xs # ys -> x ∈ xs -> x ∈ ys
ex5 #refl p = p
ex5 #swap in-head = in-tail in-head
ex5 #swap (in-tail in-head) = in-head
ex5 #swap (in-tail (in-tail p)) = in-tail (in-tail p)
ex5 (#cong π) in-head = in-head
ex5 (#cong π) (in-tail p) = in-tail (ex5 π p)
ex5 (#trans π π') p = ex5 π' (ex5 π p)

ex6 : ∀{A : Set} {x : A} (xs ys : List A) -> x ∈ xs ++ ys -> x ∈ xs ∨ x ∈ ys
ex6 [] ys p = inr p
ex6 (x :: xs) ys in-head = inl in-head
ex6 (y :: xs) ys (in-tail p) with ex6 xs ys p
... | inl q = inl (in-tail q)
... | inr q = inr q
