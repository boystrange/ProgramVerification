---
title: Lists
---

```agda
open import Fun
open import Nat
open import Equality

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

[_] : ∀{A : Set} -> A -> List A
[ x ] = x :: []

_++_ : ∀{A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : ∀{A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs

reverse : ∀{A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]

reverse-onto : ∀{A : Set} -> List A -> List A -> List A
reverse-onto []        ys = ys
reverse-onto (x :: xs) ys = reverse-onto xs (x :: ys)

fast-reverse : ∀{A : Set} -> List A -> List A
fast-reverse xs = reverse-onto xs []

length : ∀{A : Set} -> List A -> ℕ
length []        = 0
length (_ :: xs) = succ (length xs)

module Properties where

  ++-length : ∀{A : Set} (xs ys : List A) -> length (xs ++ ys) == length xs + length ys
  ++-length []        ys = refl
  ++-length (_ :: xs) ys = cong succ (++-length xs ys)

  ++-assoc : ∀{A : Set} (xs ys zs : List A) -> xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
  ++-assoc [] ys zs = refl
  ++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)

  lemma-++-[] : ∀{A : Set} (xs : List A) -> xs ++ [] == xs
  lemma-++-[] [] = refl
  lemma-++-[] (x :: xs) = cong (x ::_) (lemma-++-[] xs)

  reverse-++ : ∀{A : Set} (xs ys : List A) -> reverse (xs ++ ys) == reverse ys ++ reverse xs
  reverse-++ [] ys = symm (lemma-++-[] (reverse ys))
  reverse-++ (x :: xs) ys =
    begin
      reverse ((x :: xs) ++ ys)           ==⟨⟩
      reverse (x :: (xs ++ ys))           ==⟨⟩
      reverse (xs ++ ys) ++ [ x ]         ==⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
      (reverse ys ++ reverse xs) ++ [ x ] ==⟨ symm (++-assoc (reverse ys) (reverse xs) [ x ]) ⟩
      reverse ys ++ (reverse xs ++ [ x ]) ==⟨⟩
      (reverse ys ++ reverse (x :: xs))
    end

  reverse-involution : ∀{A : Set} (xs : List A) -> reverse (reverse xs) == xs
  reverse-involution [] = refl
  reverse-involution (x :: xs) =
    begin
      reverse (reverse (x :: xs))           ==⟨⟩
      reverse (reverse xs ++ [ x ])         ==⟨ reverse-++ (reverse xs) [ x ] ⟩
      reverse [ x ] ++ reverse (reverse xs) ==⟨⟩
      x :: reverse (reverse xs)             ==⟨ cong (x ::_) (reverse-involution xs) ⟩
      (x :: xs)
    end

  lemma-reverse-onto : ∀{A : Set} (xs ys : List A) -> reverse-onto xs ys == reverse xs ++ ys
  lemma-reverse-onto [] ys = refl
  lemma-reverse-onto (x :: xs) ys =
    begin
      reverse-onto (x :: xs) ys   ==⟨⟩
      reverse-onto xs (x :: ys)   ==⟨ lemma-reverse-onto xs (x :: ys) ⟩
      reverse xs ++ (x :: ys)     ==⟨⟩
      reverse xs ++ ([ x ] ++ ys) ==⟨ ++-assoc (reverse xs) [ x ] ys ⟩
      (reverse xs ++ [ x ]) ++ ys ==⟨⟩
      (reverse (x :: xs) ++ ys)
    end

  fast-reverse-correct : ∀{A : Set} (xs : List A) -> fast-reverse xs == reverse xs
  fast-reverse-correct xs =
    begin
      fast-reverse xs    ==⟨⟩
      reverse-onto xs [] ==⟨ lemma-reverse-onto xs [] ⟩
      reverse xs ++ []   ==⟨ lemma-++-[] (reverse xs) ⟩
      reverse xs
    end

  map-compose : ∀{A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) -> map f (map g xs) == map (f ∘ g) xs
  map-compose f g [] = refl
  map-compose f g (x :: xs) =
    begin
      map f (map g (x :: xs))       ==⟨⟩
      map f (g x :: map g xs)       ==⟨⟩
      f (g x) :: map f (map g xs)   ==⟨⟩
      (f ∘ g) x :: map f (map g xs) ==⟨ cong ((f ∘ g) x ::_) (map-compose f g xs) ⟩
      (f ∘ g) x :: map (f ∘ g) xs   ==⟨⟩
      map (f ∘ g) (x :: xs)
    end

```
