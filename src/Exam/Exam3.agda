module Exam.Exam3 where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.List
open import Library.List.Properties
open import Library.List.Permutation
open import Library.LessThan

pow : {A : Set} -> List A -> ℕ -> List A
pow _  0        = []
pow xs (succ n) = xs ++ pow xs n

++-empty : {A : Set} (xs ys : List A) -> xs ++ ys == [] -> xs == [] ∧ ys == []
++-empty [] .[] refl = refl , refl

pow-empty : {A : Set} (xs : List A) (n : ℕ) -> pow xs n == [] -> n == 0 ∨ xs == []
pow-empty xs zero p = inl refl
pow-empty xs (succ n) p with ++-empty xs (pow xs n) p
... | refl , _ = inr refl

pow-length : {A : Set} (xs : List A) (n : ℕ) -> length (pow xs n) == n * length xs
pow-length xs zero = refl
pow-length xs (succ n) =
  begin
    length (pow xs (succ n)) ==⟨ refl ⟩
    length (xs ++ pow xs n)  ==⟨ ++-length xs (pow xs n) ⟩
    length xs + length (pow xs n) ==⟨ cong (length xs +_) (pow-length xs n) ⟩
    length xs + n * length xs     ==⟨ refl ⟩
    succ n * length xs
  end

pow-comm : {A : Set} (xs : List A) (n : ℕ) -> xs ++ pow xs n == pow xs n ++ xs
pow-comm xs zero = ++-unit-r xs
pow-comm xs (succ n) =
  begin
    xs ++ pow xs (succ n) ==⟨ refl ⟩
    xs ++ (xs ++ pow xs n) ==⟨ cong (xs ++_) (pow-comm xs n) ⟩
    xs ++ (pow xs n ++ xs) ==⟨ ++-assoc xs (pow xs n) xs ⟩
    (xs ++ pow xs n) ++ xs ==⟨ refl ⟩
    pow xs (succ n) ++ xs
  end

pow-reverse : {A : Set} (xs : List A) (n : ℕ) -> pow (reverse xs) n == reverse (pow xs n)
pow-reverse xs zero = refl
pow-reverse xs (succ n) =
  begin
    pow (reverse xs) (succ n) ==⟨ refl ⟩
    reverse xs ++ pow (reverse xs) n ==⟨ cong (reverse xs ++_) (pow-reverse xs n) ⟩
    reverse xs ++ reverse (pow xs n) ==⟨ symm (reverse-++ (pow xs n) xs) ⟩
    reverse (pow xs n ++ xs) ==⟨ cong reverse (symm (pow-comm xs n)) ⟩
    reverse (xs ++ pow xs n) ==⟨ refl ⟩
    reverse (pow xs (succ n))
  end

















-- min-rec : ℕ -> ℕ -> ℕ
-- min-rec zero n = zero
-- min-rec (succ m) zero = zero
-- min-rec (succ m) (succ n) = succ (min-rec m n)

-- min-comm : (m n : ℕ) -> min-rec m n == min-rec n m
-- min-comm zero zero = refl
-- min-comm zero (succ n) = refl
-- min-comm (succ m) zero = refl
-- min-comm (succ m) (succ n) = cong succ (min-comm m n)

-- min-le-l : (m n : ℕ) -> min-rec m n <= m
-- min-le-l zero n = le-zero
-- min-le-l (succ m) zero = le-zero
-- min-le-l (succ m) (succ n) = le-succ (min-le-l m n)

-- min-le-r : (m n : ℕ) -> min-rec m n <= n
-- min-le-r zero n = le-zero
-- min-le-r (succ m) zero = le-zero
-- min-le-r (succ m) (succ n) = le-succ (min-le-r m n)

-- min-eq : (m n : ℕ) -> m == min-rec m n ∨ n == min-rec m n
-- min-eq zero n = inl refl
-- min-eq (succ m) zero = inr refl
-- min-eq (succ m) (succ n) with min-eq m n
-- ... | inl eq = inl (cong succ eq)
-- ... | inr eq = inr (cong succ eq)

-- min-min : {m n o : ℕ} -> o <= m -> o <= n -> o <= min-rec m n
-- min-min le-zero q = le-zero
-- min-min (le-succ p) (le-succ q) = le-succ (min-min p q)

-- min-le : {m n : ℕ} -> m <= n -> min-rec m n == m
-- min-le le-zero = refl
-- min-le (le-succ p) = cong succ (min-le p)
