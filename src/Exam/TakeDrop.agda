module Exam.TakeDrop where

open import Library.Nat
open import Library.List
open import Library.LessThan
open import Library.Logic
open import Library.Equality

take : {A : Set} -> ℕ -> List A -> List A
take zero     xs        = []
take (succ n) []        = []
take (succ n) (x :: xs) = x :: take n xs

drop : {A : Set} -> ℕ -> List A -> List A
drop zero     xs        = xs
drop (succ n) []        = []
drop (succ n) (x :: xs) = drop n xs

-- definire predicato Prefix xs ys (medio)

data Prefix {A : Set} : List A -> List A -> Set where
  prefix-[] : {ys : List A} -> Prefix [] ys
  prefix-:: : {x : A} {xs ys : List A} -> Prefix xs ys -> Prefix (x :: xs) (x :: ys)

take-prefix : {A : Set} (n : ℕ) (xs : List A) -> Prefix (take n xs) xs
take-prefix zero xs = prefix-[]
take-prefix (succ n) [] = prefix-[]
take-prefix (succ n) (x :: xs) = prefix-:: (take-prefix n xs)

-- facile

take-length : {A : Set} (n : ℕ) (xs : List A) -> length (take n xs) <= n
take-length zero xs = le-zero
take-length (succ n) [] = le-zero
take-length (succ n) (x :: xs) = le-succ (take-length n xs)

-- servono le-refl e le-succ-r dalla libreria (oppure occorre
-- dimostrarli)

drop-length : {A : Set} (n : ℕ) (xs : List A) -> length (drop n xs) <= length xs
drop-length zero xs = le-refl
drop-length (succ n) [] = le-zero
drop-length (succ n) (x :: xs) = le-succ-r (drop-length n xs)

take-++ : {A : Set} (n : ℕ) (xs : List A) -> ∃[ ys ] take n xs ++ ys == xs
take-++ zero     xs = xs , refl
take-++ (succ n) [] = [] , refl
take-++ (succ n) (x :: xs) with take-++ n xs
... | ys , eq = ys , cong (x ::_) eq

drop-++ : {A : Set} (n : ℕ) (xs : List A) -> ∃[ ys ] ys ++ drop n xs == xs
drop-++ zero     xs = [] , refl
drop-++ (succ n) [] = [] , refl
drop-++ (succ n) (x :: xs) with drop-++ n xs
... | ys , eq = x :: ys , cong (x ::_) eq

-- FACILE

take-drop : {A : Set} (n : ℕ) (xs : List A) -> take n xs ++ drop n xs == xs
take-drop zero xs = refl
take-drop (succ n) [] = refl
take-drop (succ n) (x :: xs) = cong (x ::_) (take-drop n xs)

-- DIFFICILE: OCCORRE DIMOSTRARE CHE EQ E` INIETTIVO

eq-inj : {A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys -> x == y ∧ xs == ys
eq-inj refl = refl , refl

take-ge : {A : Set} (n : ℕ) (xs : List A) -> take n xs == xs -> length xs <= n
take-ge zero .[] refl = le-zero
take-ge (succ n) [] eq = le-zero
take-ge (succ n) (x :: xs) eq = le-succ (take-ge n xs (snd (eq-inj eq)))

-- dem : {A B : Set} -> A ∧ B -> ¬ (¬ A ∨ ¬ B)
-- dem (x , y) (inl p) = p x
-- dem (x , y) (inr p) = p y
