---
title: Programming with lists
prev:  Chapter.Intro.Polymorphism
---

```
module Chapter.Intro.Lists where
```

Lists are a fundamental data structure for the representation of
**finite sequences** of elements. In this section we define the
`List` data type and prove a few properties of functions that
manipulate lists.

## Imports

```
open import Library.Fun
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.Nat
```

## Data types with parameters

It is easy to define an Agda data type of lists, observing that
every list of elements of type `A` can be either

* the **empty list**, or
* a non empty list with a **head** of type `A` (the first element of
  the list) and a **tail** which is itself a list of elements of
  type `A`.

We would like to define the list data type once and for all,
independently of the type `A` of its elements. For this, we
introduce a **parameter** into the data type.

```
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A
```

According to this definition, `List` by itself is not a
type. Rather, it is a function that, when applied to an arbitrary
type `A`, yields the type of lists with elements of type `A`. You
can verify this claim by entering `C-c C-d List`. Notice that the
parameter `A` is declared right after the name of the data type and
its scope covers all the constructors of the data type, in which it
becomes an implicit argument. In line with the syntax adopted in
many functional languages, we have chosen to write `[]` for the
empty list and `x :: xs` for the list with head `x` and tail
`xs`. We declare `::` as a right associative operator so as to make
it easy to write lists by repeated applications of `::`.

```
infixr 5 _::_
```

For example, the following list contains the first four natural
numbers.

```
_ : List ℕ
_ = 0 :: 1 :: 2 :: 3 :: []
```

## Basic operations on lists

As noted above, each constructor of lists carries an implicit
argument `A` standing for the type of the elements of the list being
constructed. We have to bear this aspect in mind when we define
functions that manipulate lists. For example, the following function
creates a list containing a single element.

```
[_] : ∀{A : Set} -> A -> List A
[_] = _:: []
```

Now we can write `[ 0 ]` for the list consisting of the sole element
`0` or `[ true ]` for the list consisting of the sole element
`true`. The type of the elements of these lists is inferred
automatically by Agda. If we want to write the implicit argument
explicitly, we have to resort to the prefix notation: `[_] {ℕ} 0` is
the singleton list made of `0` and `[_] {Bool} true` is the
singleton list made of `true`.

As another example, below is the function that computes the length
of a list.

```
length : ∀{A : Set} -> List A -> ℕ
length []        = 0
length (_ :: xs) = succ (length xs)
```

## List concatenation

We now define list concatenation and prove a few essential
properties about it. List concatenation, denoted by the infix
operator `++`, is defined by structural recursion on the left
operand.

```
_++_ : ∀{A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
```

We stipulate that `++` is right associative and has the same
priority as `::`. In this way, we can write lists by mixing `::` and
`++` without using too many parentheses.

```
infixr 5 _++_
```

A first obvious fact about `++` is that the length of the
concatenation of two lists is the sum of the lengths of the two
lists.

```
length-++ : ∀{A : Set} (xs ys : List A) -> length (xs ++ ys) == length xs + length ys
length-++ []        ys = refl
length-++ (_ :: xs) ys = cong succ (length-++ xs ys)
```

Also, list concatenation is associative.

```
++-assoc : ∀{A : Set} (xs ys zs : List A) -> xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
++-assoc []        ys zs = refl
++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)
```

The empty list `[]` acts as left and right unit for list
concatenation. On the left, this property follows from the very
definition of list concatenation.

```
++-unit-l : ∀{A : Set} (xs : List A) -> xs == [] ++ xs
++-unit-l _ = refl
```

On the right, we prove the result by structural induction on the list.

```
++-unit-r : ∀{A : Set} (xs : List A) -> xs == xs ++ []
++-unit-r [] = refl
++-unit-r (x :: xs) =
  begin
    x :: xs         ==⟨ cong (x ::_) (++-unit-r xs) ⟩
    x :: (xs ++ []) ==⟨ refl ⟩
    (x :: xs) ++ []
  end
```

Note that list concatenation is not commutative in general.

## Reversing a list

We now define a function `reverse` that, as the name suggests,
reverses the order of the elements in a list. There are several ways
of defining this function and the version we show here is simple but
also inefficient.

```
reverse : ∀{A : Set} -> List A -> List A
reverse []        = []
reverse (x :: xs) = reverse xs ++ [ x ]
```

Intuitively, reversing the empty list yields the empty list and
reversing a list with head `x` and tail `xs` yields a list whose
prefix is the reverse of `xs` and whose last element is `x`. Note
the use of the operator `[_]` which is necessary as concatenation is
defined on lists, not on single elements of lists. As an example,
entering `C-c C-n reverse (0 :: 1 :: 2 :: 3 :: [])` yields `3 :: 2
:: 1 :: 0 :: []`.

We expect `reverse` to be an *involution*, namely a function that is
the inverse of itself. Before proving this property, it is necessary
to show how `reverse` behaves on the concatenation of two lists. Not
surprisingly, reversing the concatenation of two lists yields the
concatenation of the two lists reversed, but in the *reverse order*!

```
reverse-++ : ∀{A : Set} (xs ys : List A) -> reverse (xs ++ ys) == reverse ys ++ reverse xs
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

We can now show that `reverse` is an involution.

```
reverse-inv : ∀{A : Set} (xs : List A) -> reverse (reverse xs) == xs
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

The reason why the provided definition of `reverse` is inefficient
is that it makes use of concatenation to move the first element of a
list to the end of its reverse. Since concatenation is defined by
structural induction on the leftmost list, this means that the cost
of computing `reverse xs` is proportional to $n^2$ if $n$ is the
length of `xs`. In order to obtain a more efficient version of
`reverse` we start by defining a slightly more general function
called `reverse-onto`, which "moves" the elements of one list in
front of another list. Since the elements are moved one by one, the
effect is that of reversing the first list "onto" the second one.

```
reverse-onto : ∀{A : Set} -> List A -> List A -> List A
reverse-onto []        ys = ys
reverse-onto (x :: xs) ys = reverse-onto xs (x :: ys)
```

For exampe, entering `C-c C-n reverse-onto (1 :: 2 :: 3 :: []) [ 4
]` yields `3 :: 2 :: 1 :: 4 :: []`. In particular, we can obtain an
alternative way of computing `reverse xs` as `reverse-onto xs
[]`. The advantage of this approach is that `reverse-onto` is only
defined in terms of `::`, whose complexity is constant.

```
fast-reverse : ∀{A : Set} -> List A -> List A
fast-reverse xs = reverse-onto xs []
```

In order to show that `fast-reverse` and `reverse` are in fact two
different implementations of the same function we need the following
auxiliary result, relating `reverse-onto` and `reverse`.

```
lemma-reverse-onto : ∀{A : Set} (xs ys : List A) -> reverse-onto xs ys == reverse xs ++ ys
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
```

We can now complete the proof of `fast-reverse xs == reverse xs`.

```
fast-reverse-correct : ∀{A : Set} (xs : List A) -> fast-reverse xs == reverse xs
fast-reverse-correct xs =
  begin
    fast-reverse xs    ==⟨ refl ⟩
    reverse-onto xs [] ==⟨ lemma-reverse-onto xs [] ⟩
    reverse xs ++ []     ⟨ ++-unit-r (reverse xs) ⟩==
    reverse xs
  end
```

## Exercises

Let `map` be the function defined below.

```
map : ∀{A B : Set} -> (A -> B) -> List A -> List B
map f []        = []
map f (x :: xs) = f x :: map f xs
```

1. Prove that `length (map f xs) == length xs`
2. Prove that `map f (xs ++ ys) == map f xs ++ map f ys`
3. Prove that `map f (reverse xs) == reverse (map f xs)`
4. Prove that `(map f ∘ map g) xs == map (f ∘ g) xs`

```
map-length : ∀{A B : Set} (f : A -> B) (xs : List A) -> length (map f xs) == length xs
map-length f [] = refl
map-length f (x :: xs) = cong succ (map-length f xs)

map-++ : ∀{A B : Set} (f : A -> B) (xs ys : List A) -> map f (xs ++ ys) == map f xs ++ map f ys
map-++ f []        ys = refl
map-++ f (x :: xs) ys = cong (f x ::_) (map-++ f xs ys)

map-reverse : ∀{A B : Set} (f : A -> B) (xs : List A) -> map f (reverse xs) == reverse (map f xs)
map-reverse f [] = refl
map-reverse f (x :: xs) =
  begin
    map f (reverse (x :: xs))                   ==⟨ refl ⟩
    map f (reverse xs ++ [ x ])                 ==⟨ map-++ f (reverse xs) [ x ] ⟩
    map f (reverse xs) ++ map f [ x ]           ==⟨ cong (_++ map f [ x ]) (map-reverse f xs) ⟩
    reverse (map f xs) ++ map f [ x ]           ==⟨ refl ⟩
    reverse (map f xs) ++ reverse (map f [ x ]) ==⟨ reverse-++ (map f [ x ]) (map f xs) ⟩
    reverse (map f [ x ] ++ map f xs)           ==⟨ refl ⟩
    reverse (map f (x :: xs))
  end

map-∘ : ∀{A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) ->
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
{:.solution}

<!--
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
-->
