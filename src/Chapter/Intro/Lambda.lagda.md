---
title: Types and functions
next:  Chapter.Intro.Bool
---

<!--
```
module Chapter.Intro.Lambda where
```
-->

To try out the examples discussed in this chapter and to solve the
proposed exercises it is necessary to include the `Nat` module,
which defines the natural numbers and some basic operations on
them. We will discuss natural numbers in a [dedicated chapter]({%
link pages/Chapter.Intro.NaturalNumbers.md %}). For the time being, we
simply import the module and make its content accessible by means of
the following clause.

```
open import Nat
```

## Simple types

Agda is a strongly typed programming language and every term of the
language must be **well typed** in order to be considered by
Agda. For now we only consider a small set of **simple types**:

* `ℕ` stands for the type of **natural numbers**;
* if `A` and `B` are types, then `(A -> B)` is the type of
  **functions** that, when applied to an argument of type `A`, yield a
  *result of type `B`.

To limit the amount of parentheses we have to write in types and to
improve readability, we adopt the following conventions:

* we omit topmost parentheses, so that `A -> B` stands for `(A -> B)`;
* we assume that `->` associates to the **right**, so that e.g. `A
  -> B -> C` stands for `A -> (B -> C)` and not for `(A -> B) -> C`.

## Terms

We assume the existence of an infinite set of **term variables** `{
x, y, z, ... }` often called simply variables. Agda is a strongly
typed language, in the sense that it only considers (and evaluates)
terms that are **well typed** according to a specific set of
**typing rules**. In describing the syntax of terms, we also
informally describe the typing rules that they must obey and how
their type is determined.

* A variable of type `A` is also a term of type `A`.
* If `x` is a variable, `A` is a type and `M` is a term of type `B`
  assuming that `x` has type `A`, then `(λ (x : A) -> M)` is a term
  of type `A -> B` called **abstraction** and represents a function
  that produces `M` when applied to `x`. We say that `x` is the
  **argument** of the function and that `M` is its **body**.
* If `M` is a term of type `A -> B` and `N` is a term of type `A`,
  then `(M N)` is a term of type `B` called **application** and
  represents the application of (the function) `M` to (the argument)
  `N`. It is useful to think of function application as of an
  invisible operator placed in between `M` and `N`.

We will introduce new terms in the following chapters. For the time
being, since we have imported the `Nat` module from the library, a
number of terms defined therein are also available. In particular:

* `zero` of type `ℕ` represents the natural number zero;
* `succ` of type `ℕ -> ℕ` is a function that, applied to a natural
  number, yields its successor.

The usual decimal notation for natural numbers is also available, so
that `0` can be used as abbreviation for `zero`, `2` can be used for
abbreviation for `succ (succ zero)` and `42` can be used for
abbreviation for 42 applications of `succ` to `zero`.

As for types, also for terms we adopt some syntactic conventions to
improve readability.

* We omit topmost parentheses, so that e.g. `M N` stands for `(M
  N)`.
* We omit the type of an argument when it is unimportant or clear
  from the context. For example, we may write `λ x -> x` instead of
  `λ (x : A) -> x`.
* We often collapse nested abstractions into one, so that e.g. `λ x
  y z -> M` stands for `λ x -> λ y -> λ z -> M`.
* We assume that the body of an abstraction extends as much as
  possible to the right. For example, `λ x y -> x y` stands for `λ x
  y -> (x y)` and not for `(λ x y -> x) y`.
* We assume that application is **left associative**, so that `M₁ M₂
  M₃` stands for `(M₁ M₂) M₃` and not for `M₁ (M₂ M₃)`.

## Definitions

An Agda program consists mainly of **definitions** with which we
give names to terms and we specify their type. For example, the
following two lines specify that `f` is a function of type `ℕ -> ℕ`
that maps $x$ to $x^2 + 1$:

```
f : ℕ -> ℕ
f = λ x -> x ^ 2 + 1
```

The first line provides the **signature** of `f`. Top-level
definitions like this one must always be accompanied by a
signature. The second line provides the **definition** of `f` with
which we establish that `f` is **definitionally** the same as the
abstraction `λ x - x ^ 2 + 1`. That is, for Agda the name `f` and
the term `λ x -> x ^ 2 + 1` are definitionally the same thing. Note
that we omit the type of the argument `x` for this abstraction: Agda
is able to figure out that `x` has type `ℕ` from both the signature
of `f` and the fact that the operators `^` and `+` concern natural
numbers.

A note on **spacing** in Agda: unlike most programming languages,
Agda allows almost any character to be part of an identifier. For
example, `^` and `+` are plain Agda identifiers just like `f` and
`ℕ`. If we write `x^2` (without spaces around `^`), Agda considers
this a single identifier (for which we have provided no definition).

By loading the program using `C-c C-l`, Agda verifies that `f` is
well typed and that its type is consistent with the one provided in
its signature.  We can verify the behavior of `f` by applying it to
some natural numbers. For example, if we hit `C-c C-n` and enter `f
2` we obtain `5` as result. The command `C-c C-n` asks Agda to
*evaluate* (technically, to *normalize*), the provided expression.

When defining abstractions, Agda provides an alternative, more
convenient notation with which argument and body of the function are
separated by the symbol `=` . For example, an equivalent way of
defining `f` is

```
f₁ : ℕ -> ℕ
f₁ x = x ^ 2 + 1
```

which can be read as "`f₁` applied to `x` is definitionally the same
as `x ^ 2 + 1`". We have named this alternative definition of the
function `f₁` instead of `f` to avoid a *name clash*: there cannot
be two definitions with the same name in the same Agda file. Here
and in the following chapters we will use indices when providing
multiple versions of the same definition.

## Multi-argument and higher-order functions

Strictly speaking, all Agda functions have exactly one argument. The
usual way of representing multi-argument functions in a functional
language like Agda is by means of functions that yield other
functions as result. For example, `g` below is defined as a function
that maps $x$ to a function that maps $y$ to $x^2 + 2xy + 1$.

```
g : ℕ -> ℕ -> ℕ
g = λ x -> λ y -> x ^ 2 + 2 * x * y + 1
```

Equivalently, `g` can be written as follows:

```
g₁ : ℕ -> ℕ -> ℕ
g₁ x y = x ^ 2 + 2 * x * y + 1
```

We can use `C-c C-n` to verify that `g 2 3` evaluates to `17`. Since
function application is left associative, `g 2 3` is the same as `(g
2) 3`. That is, we first apply `g` to `2` to obtain the function

    λ y -> 2 ^ 2 + 2 * 2 * y + 1

and then we apply this function to `3`, to obtain
`2 ^ 2 + 2 * 2 * 3 + 1` that is `17`.

As in most functional programming languages, functions are
first-class entities that can be provided as arguments and returned
as results of other functions. For example, the function

```
twice : (ℕ -> ℕ) -> ℕ -> ℕ
twice f x = f (f x)
```

applied to a function `f` and an argument `x` applies `f` to `x`
twice. Evaluating `twice f 2` where `f` is the function defined
above yields `26`.

## Exercises

1. Define at least six different versions of the function that
   computes the successor of a natural number.
2. Which of the following terms are well typed? Use Agda to verify
   whether your answers are correct.
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ -> ℕ) -> x y`
   * `λ (x : (ℕ -> ℕ) -> ℕ) (y : ℕ) -> x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x (x y)`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x y y`

```
-- EXERCISE 1

succ₁ : ℕ -> ℕ
succ₁ = succ

succ₂ : ℕ -> ℕ
succ₂ x = succ x

succ₃ : ℕ -> ℕ
succ₃ = λ x -> x + 1

succ₄ : ℕ -> ℕ
succ₄ = λ x -> 1 + x

succ₅ : ℕ -> ℕ
succ₅ x = x + 1

succ₆ : ℕ -> ℕ
succ₆ x = 1 + x
```
