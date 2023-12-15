
open import Library.Nat
open import Library.List
open import Library.LessThan
open import Library.Logic
open import Library.Equality

take : ∀{A : Set} -> ℕ -> List A -> List A
take zero     xs = []
take (succ n) [] = []
take (succ n) (x :: xs) = x :: take n xs

ex1 : ∀{A : Set} (n : ℕ) (xs : List A)
      -> length (take n xs) <= length xs
ex1 zero     xs = le-zero
ex1 (succ n) [] = le-zero
ex1 (succ n) (x :: xs) = le-succ (ex1 n xs)

data Prefix {A : Set} : List A -> List A -> Set where
  prefix-[] : ∀{ys : List A} -> Prefix [] ys
  prefix-:: : ∀{x : A} {xs ys : List A} ->
              Prefix xs ys -> Prefix (x :: xs) (x :: ys)

_ : Prefix (0 :: 1 :: []) (0 :: 1 :: 2 :: 3 :: 4 :: [])
_ = prefix-:: (prefix-:: prefix-[])

ex3 : ∀{A : Set} (n : ℕ) (xs : List A) ->
      Prefix (take n xs) xs
ex3 zero     xs = prefix-[]
ex3 (succ n) [] = prefix-[]
ex3 (succ n) (x :: xs) = prefix-:: (ex3 n xs)

ex4 : ∀{A : Set} (n : ℕ) (xs : List A) ->
      ∃[ ys ] take n xs ++ ys == xs
ex4 zero xs = xs , refl
ex4 (succ n) [] = [] , refl
ex4 (succ n) (x :: xs) with ex4 n xs
... | ys , eq = ys , cong (x ::_) eq

ex5 : ∀{A : Set} {x y : A} {xs ys : List A} ->
      x :: xs == y :: ys -> x == y ∧ xs == ys
ex5 refl = refl , refl

ex6 : ∀{A B : Set} -> A ∧ B -> (¬ A ∨ ¬ B) -> ⊥
ex6 (pa , pb) (inl p) = p pa
ex6 (pa , pb) (inr p) = p pb
