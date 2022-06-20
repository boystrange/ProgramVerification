---
title: Programming with lists
---

<!--
```
module Chapter.Lists where

open import Fun
open import Equality
open import Equality.Reasoning
open import Nat
```
-->

Lists are a fundamental data structure for the representation of
**finite sequences** of elements. It is easy to define an Agda data
type of lists, considering that every list of elements of type `A`
can be either

* the **empty list**, or
* a non empty list with a **head** of type `A` (the first element of
  the list) and a **tail** which is itself a list of elements of
  type `A`.

Nonetheless, we would like to define the list data type once and for
all, independently of the type `A` of its elements. For this, we
introduce a **parameter** into the data type.

```
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A
```

According to this definition, `List` by itself is not a
type. Rather, it is a function that, applied to an arbitrary type
`A`, yields the type of lists with elements of type `A`. Notice that
the paramtere `A` is declared type right after the name of the data
type and its scope covers all the constructors of the data type. In
line with the syntax adopted in many functional languages, we have
chosen to write `[]` for the empty list and `x :: xs` for the list
with head `x` and tail `xs`.

We declare `::` as a right associative operator so as to make it
easy to write lists by repeated applications of `::`.

```
infixr 5 _::_
```

For example, the following list contains the first four natural
numbers.

```
_ : List ℕ
_ = 0 :: 1 :: 2 :: 3 :: []
```

IMPLICIT PARAMETERS

```
[_] : {A : Set} -> A -> List A
[ x ] = x :: []
```

```
length : {A : Set} -> List A -> ℕ
length []        = 0
length (_ :: xs) = succ (length xs)
```

## List concatenation

```
_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys        = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
```

```
infixr 5 _++_
```

```
length-++ : {A : Set} (xs ys : List A) -> length (xs ++ ys) == length xs + length ys
length-++ [] ys        = refl
length-++ (_ :: xs) ys = cong succ (length-++ xs ys)
```

```
++-assoc : {A : Set} (xs ys zs : List A) -> xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
++-assoc [] ys zs        = refl
++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)
```

```
++-unit-r : {A : Set} (xs : List A) -> xs == xs ++ []
++-unit-r [] = refl
++-unit-r (x :: xs) =
  begin
    x :: xs         ==⟨ cong (x ::_) (++-unit-r xs) ⟩
    x :: (xs ++ []) ==⟨ refl ⟩
    (x :: xs) ++ []
  end
```

## Reversing a list

```
reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ [ x ]
```

```
reverse-++ : {A : Set} (xs ys : List A) -> reverse (xs ++ ys) == reverse ys ++ reverse xs
reverse-++ [] ys        = ++-unit-r (reverse ys)
reverse-++ (x :: xs) ys =
  begin
    reverse ((x :: xs) ++ ys)           ==⟨ refl ⟩
    reverse (x :: (xs ++ ys))           ==⟨ refl ⟩
    reverse (xs ++ ys) ++ [ x ]         ==⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]   ⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩==
    reverse ys ++ (reverse xs ++ [ x ]) ==⟨ refl ⟩
    reverse ys ++ (reverse (x :: xs))
  end
```

```
reverse-inv : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-inv [] = refl
reverse-inv (x :: xs) =
  begin
    reverse (reverse (x :: xs))           ==⟨ refl ⟩
    reverse (reverse xs ++ [ x ])         ==⟨ reverse-++ (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs) ==⟨ refl ⟩
    x :: reverse (reverse xs)             ==⟨ cong (x ::_) (reverse-inv xs) ⟩
    x :: xs
  end
```

## A more efficient `reverse`

```
reverse-onto : {A : Set} -> List A -> List A -> List A
reverse-onto [] ys        = ys
reverse-onto (x :: xs) ys = reverse-onto xs (x :: ys)

fast-reverse : {A : Set} -> List A -> List A
fast-reverse xs = reverse-onto xs []

lemma-reverse-onto : {A : Set} (xs ys : List A) -> reverse-onto xs ys == reverse xs ++ ys
lemma-reverse-onto [] ys = refl
lemma-reverse-onto (x :: xs) ys =
  begin
    reverse-onto (x :: xs) ys   ==⟨ refl ⟩
    reverse-onto xs (x :: ys)   ==⟨ lemma-reverse-onto xs (x :: ys) ⟩
    reverse xs ++ (x :: ys)     ==⟨ refl ⟩
    reverse xs ++ ([ x ] ++ ys) ==⟨ ++-assoc (reverse xs) [ x ] ys ⟩
    (reverse xs ++ [ x ]) ++ ys ==⟨ refl ⟩
    reverse (x :: xs) ++ ys
  end

fast-reverse-correct : {A : Set} (xs : List A) -> fast-reverse xs == reverse xs
fast-reverse-correct xs =
  begin
    fast-reverse xs    ==⟨ refl ⟩
    reverse-onto xs [] ==⟨ lemma-reverse-onto xs [] ⟩
    reverse xs ++ []     ⟨ ++-unit-r (reverse xs) ⟩==
    reverse xs
  end
```

## Exercises

Let `map` be the function defined

```
map : {A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs
```

```
map-∘ : {A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) ->
  (map f ∘ map g) xs == map (f ∘ g) xs
map-∘ f g [] = refl
map-∘ f g (x :: xs) =
  begin
    (map f ∘ map g) (x :: xs)       ==⟨ refl ⟩
    map f (map g (x :: xs))         ==⟨ refl ⟩
    map f (g x :: map g xs)         ==⟨ refl ⟩
    f (g x) :: map f (map g xs)     ==⟨ refl ⟩
    (f ∘ g) x :: (map f ∘ map g) xs ==⟨ cong ((f ∘ g) x ::_) (map-∘ f g xs) ⟩
    (f ∘ g) x :: map (f ∘ g) xs     ==⟨ refl ⟩
    map (f ∘ g) (x :: xs)
  end
```

1. Prove that `length (map f xs) == length xs`
2. Prove that `(map f ∘ map g) xs == map (f ∘ g) xs`

Let `foldl` and `foldr` be the functions defined

```
foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f a [] = a
foldr f a (x :: xs) = f x (foldr f a xs)
```

```
foldl : {A B : Set} -> (A -> B -> A) -> A -> List B -> A
foldl f a [] = a
foldl f a (x :: xs) = foldl f (f a x) xs
```

```
foldl-reverse-onto : {A : Set} (xs ys : List A) -> foldl (flip _::_) ys xs == reverse-onto xs ys
foldl-reverse-onto [] ys = refl
foldl-reverse-onto (x :: xs) ys =
  begin
    foldl (flip _::_) ys (x :: xs) ==⟨ refl ⟩
    foldl (flip _::_) (x :: ys) xs ==⟨ foldl-reverse-onto xs (x :: ys) ⟩
    reverse-onto xs (x :: ys)      ==⟨ refl ⟩
    reverse-onto (x :: xs) ys
  end

foldl-reverse : {A : Set} (xs : List A) -> foldl (flip _::_) [] xs == reverse xs
foldl-reverse xs =
  begin
    foldl (flip _::_) [] xs ==⟨ foldl-reverse-onto xs [] ⟩
    reverse-onto xs []      ==⟨ refl ⟩
    fast-reverse xs         ==⟨ fast-reverse-correct xs ⟩
    reverse xs
  end
```
