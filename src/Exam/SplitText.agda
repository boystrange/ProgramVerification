module Exam.SplitText where

-- RULES

-- You **cannot consult any teaching material** (Moodle page,
-- lecture notes, etc.)

-- You can **look at** and **import** any module from the Agda
-- library used in the lectures.

-- You can **define any auxiliary function** in addition to the
-- requested results.

-- You have **45 minutes** to complete the assignment. When the time
-- is over, submit your assignment by sending an email to
-- <luca.padovani@unicam.it>.

-- Be ready to **explain** any part of the code you submit.

-- GIVEN DEFINITIONS

open import Library.Nat
open import Library.List
open import Library.Equality

data Split {A : Set} : List A -> List A -> List A -> Set where
  split-[] : Split [] [] []
  split-l : {x : A} {xs ys zs : List A} -> Split xs ys zs ->
            Split (x :: xs) (x :: ys) zs
  split-r : {x : A} {xs ys zs : List A} -> Split xs ys zs ->
            Split (x :: xs) ys (x :: zs)

-- EXERCISE 0 (4 POINTS)

-- What is the relation between xs, ys and zs if we have a proof of
-- (namely a term of type) Split xs ys zs? Provide an explanation in
-- natural language. You might want to try solving some of the next
-- 2/3 exercises before writing the answer.

-- EXERCISE 1 (4 POINTS)

split-refl : {A : Set} (xs : List A) -> Split xs [] xs
split-refl = {!!}

-- EXERCISE 2 (4 POINTS)

split-++ : {A : Set} (xs ys : List A) -> Split (xs ++ ys) xs ys
split-++ = {!!}

-- EXERCISE 3 (4 POINTS)

split-comm : {A : Set} {xs ys zs : List A} -> Split xs ys zs -> Split xs zs ys
split-comm = {!!}

-- EXERCISE 4 (14 POINTS)

-- Define a function sum that computes the sum of the elements of a
-- list of natural numbers.

sum : List ℕ -> ℕ
sum = {!!}

-- Prove the following result.

split-sum : {xs ys zs : List ℕ} -> Split xs ys zs -> sum xs == sum ys + sum zs
split-sum = {!!}
