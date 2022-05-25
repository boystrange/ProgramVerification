---
title: First steps with Agda
---

## Sets and types

* both sets and types are collections of elements, but in set theory
* the same element can belong to different sets, whereas in type
  theory every element inhabits exactly one type
* typical operations on sets are support union, intersection,
  cartesian product, arrow is function space
* typical operations on types are cartesian product, disjoint union

To try out the examples discussed in this section and to solve the
proposed exercises it is necessary to include the `Product` module,
which defines the cartesian product for types. We will understand
its definition in a [later section](???).

```agda
open import Product
```

## Simple types

We assume the existence of an infinite set of **type names** `{ α,
β, γ, ... }`. The syntax of **types** in the simply typed λ calculus
is defined by the following grammar

```text
  A, B ::= α | (A -> B) | (A × B)
```

where `(A -> B)` is called **arrow type** or **function type** and
`(A × B)` is called **product type** or **pair type**. Intuitively,
`(A -> B)` is the type of functions taking an argument of type `A`
and producing a result of type `B`, whereas `(A × B)` is the type of
pairs whose components have type `A` and `B` respectively.

Hereafter, type names may stand for unknown types but also for basic
or predefined types, such as the type `ℕ` of natural numbers, the
type `Bool` of boolean values, the type `String` of strings, and so
forth.

To limit the amount of parentheses we have to write in types, we
adopt the following conventions:

* We omit topmost parentheses, so that `A -> B` stands for `(A -> B)`

* We assume that `×` has higher precedence than `->`, so that `A × B
  -> A` stands for `(A × B) -> A` and not for `A × (B -> A)`

* We assume that `->` and `x` associate to the **right**, so that
  e.g. `A -> B -> C` stands for `A -> (B -> C)` and not for `(A ->
  B) -> C`. Similarly, `A × B × C` stands for `A × (B × C)`.

## Terms

We assume the existence of an infinite set of **term variables** `{
x, y, z, ... }` often called simply variables. The syntax of
**terms** is defined by the following grammar

```text
  M, N ::= x | (λ (x : A) -> M) | (M N) | (M , N) | fst | snd
```

where:

* a term of the form `(λ (x : A) -> M)` is called **abstraction**
  representing a function that produces `M` when applied to `x`. We
  say that `x` is the **argument** of the function and that `M` is
  its **body**;
* a term of the form `(M N)` is called **application** and
  represents the application of (the function) `M` to (the argument)
  `N`. It is useful to think of function application as of an
  invisible operator placed in between `M` and `N`;
* a term of the form `(M , N)` is called **pair** and represents a
  pair whose components are `M` and `N`;
* the terms `fst` and `snd` are called **pair projections** and
  denote the functions that respectively return the first and second
  component of their argument.

As for types, we adopt some syntactic conventions to improve the
readability of terms. In particular:

* We omit topmost parentheses, so that e.g. `M N` stands for `(M
  N)`;
* We omit the type of an argument when it is unimportant or clear
  from the context. For example, we may write `λ x -> x` instead of
  `λ (x : A) -> x`;
* We collapse subsequent abstractions into one, so that e.g. `λ x y
  z -> M` stands for `λ x -> λ y -> λ z -> M`;
* We assume that the body of a lambda abstraction extends as much as
  possibly to the right. For example, `λ x y -> x y` stands for `λ x
  y -> (x y)` and not for `(λ x y -> x) y`;
* We assume that application is **left associative**, so that `M₁ M₂
  M₃` stands for `(M₁ M₂) M₃` and not for `M₁ (M₂ M₃)`;
* We assume that application has **higher precedence** than `,` and
  of any other operator that will be introduced later. For example,
  `M N₁ , N₂` stands for `(M N₁) , N₂` and not for `M (N₁ ,
  N₂)`. This convention applies also to the projections `fst` and
  `snd` (which, as we will see, are just special instances of
  function applications);
* We assume that pair formation is **right associative**, so that
  e.g. `M₁ , M₂ , M₃` stands for `M₁ , (M₂ , M₃)` and not for `(M₁ ,
  M₂) , M₃`;

## Currying

## Well-typed terms

```text

  [VAR]  -----------------
         Γ, x : A |- x : A
```

```text
             Γ, x : A |- M : B
  [LAM]  ---------------------------
         Γ |- λ(x : A) -> M : A -> B
```

```text
         Γ |- M : A -> B    Γ |- N : A
  [APP]  -----------------------------
                 Γ |- M N : B
```

```text
  [PAIR]                      [FST]             [SND]
  Γ |- M : A    Γ |- N : B    Γ |- M : A × B    Γ |- M : A × B
  ------------------------    --------------    --------------
    Γ |- (M , N) : A × B      Γ |- fst M : A    Γ |- snd M : B
```

## Definitions

Define a few types and terms


```agda
postulate A B C : Set

id : A -> A
id = λ(x : A) -> x

id₂ : A -> A
id₂ = λ x -> x

id₃ : A -> A
id₃ x = x
```

```agda

-- esercizio
curry : (A × B -> C) -> A -> B -> C
curry f x y = f (x , y)

uncurry : (A -> B -> C) -> A × B -> C
uncurry f p = f (fst p) (snd p)

```

## Homework

While solving the following exercises, try to minimize the use of
parentheses taking advantage of the established syntactic
conventions.

1. Implement the function `swap : A × B -> B × A`.
2. Implement the function `flip : (A -> B -> C) -> B -> A -> C`.
3. Implement the function `rotate : A × B × C -> C × A × B`.
4. Implement the function `compose : (B -> C) -> (A -> B) -> A -> C`.
5. Provide two syntactically different (but equivalent)
   implementations of the function `apply : (A -> B) -> A -> B`.

```agda
swap : A × B -> B × A
swap p = snd p , fst p

flip : (A -> B -> C) -> B -> A -> C
flip = λ f x y -> f y x

rotate : A × B × C -> C × A × B
rotate = λ x -> snd (snd x) , fst x , fst (snd x)

compose : (B -> C) -> (A -> B) -> A -> C
compose f g = λ x -> f (g x)

apply₁ : (A -> B) -> A -> B
apply₁ f x = f x

apply₂ : (A -> B) -> A -> B
apply₂ x = x
```
{:.solution}

Which of the following terms are well typed? Verify your answer
using Agda and come up with justifications for the ill-typed terms.

1. `λ (x : A) -> (x , x)`
2. `λ (f : A -> A) (x : B) -> f x`
3. `λ (x : A -> A) -> x x`
4. `(fst , snd)`
5. `fst λ (x : A) -> x`
6. `snd (λ (x : A) -> x , fst)`
