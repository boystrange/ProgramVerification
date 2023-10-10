---
title: Types and functions
next:  Chapter.Intro.Bool
---

```
module Chapter.Intro.Lambda where
```

## Imports

To try out the examples discussed in this chapter and to solve the
proposed exercises it is necessary to import the `Nat` module, which
defines the natural numbers and some basic operations on them. We
will see how natural numbers are defined in a [dedicated
chapter](Chapter.Intro.NaturalNumbers.html). For the time being, we
simply import the module and make its content accessible by means of
the following clause.

```
open import Library.Nat
```

## Simple types

Agda is a strongly typed programming language and every term of the
language must be **well typed** in order to be considered by
Agda. For now we only consider a small set of **simple types**:

* `ℕ` stands for the type of **natural numbers**;
* if `A` and `B` are types, then `(A -> B)` is the type of
  **functions** that, when applied to an argument of type `A`, yield a
  result of type `B`.

To limit the amount of parentheses we have to write in types and to
improve readability, we adopt the following conventions:

* we omit topmost parentheses, so that `A -> B` stands for `(A -> B)`;
* we assume that `->` associates to the **right**, so that e.g. `A
  -> B -> C` stands for `A -> (B -> C)` and not for `(A -> B) -> C`.

## Defining functions

An Agda function is written as a term of the form `λ (x : A) -> M`
where

* `x` is the **name of the argument** of the function;
* `A` is the **type of the argument** of the function;
* `M` is the **body** of the function, namely the expression that
  computes the result of applying the function to its argument.

Below are a few simple examples of functions that make use of types
and operators defined in the `Nat` module:

* `λ (x : ℕ) -> x` is the identity function for natural numbers;
* `λ (x : ℕ) -> x + 1` is the successor function for natural numbers;
* `λ (x : ℕ) -> x ^ 2 + 1` is the function that, applied to a
  natural number $x$, computes $x^2 + 1$.

All of these functions have type `ℕ -> ℕ` since they accept a
natural number as argument (the `ℕ` to the lhs of `->`) and produce
a natural number as result (the `ℕ` to the rhs of `->`).  The type
annotation of the argument can be omitted when its type can be
inferred from the context. For example, since the `+` and `^`
operators defined in the `Nat` module can only be applied to natural
numbers, the last two functions above can be more concisely written
as `λ x -> x + 1` and `λ x -> x ^ 2 + 1` respectively. We can verify
this by asking Agda to compute the type of these functions. This is
achieved by typing `C-c C-d` followed by the function (more
generally the term) for which we want Agda to infer the type.

All the examples above define **anonymous functions**, functions
without a name that are defined "on the spot", wherever we need. It
if often convenient to give names to functions, especially if we
plan to apply them multiple times or if we want to make them
available in a library or a complex Agda development. In an Agda
**program** we can use **definitions** to give names to terms and to
specify their type. For example, the program containing the
following two lines specify that `f` is a function of type `ℕ -> ℕ`
that maps $x$ to $x^2 + 1$:

```
f : ℕ -> ℕ
f = λ x -> x ^ 2 + 1
```

The first line provides the **signature** of `f`. Top-level
definitions like this one must always be accompanied by a
signature. The second line provides the **definition** of `f` with
which we establish that the name `f` is **definitionally** the same
as the abstraction `λ x -> x ^ 2 + 1`. That is, for Agda the name
`f` and the term `λ x -> x ^ 2 + 1` are **equal**. Note that we omit
the type of the argument `x` for this abstraction, since Agda is
able to figure out that `x` has type `ℕ` from both the signature of
`f` and the fact that the operators `^` and `+` concern natural
numbers. Speaking of these operators, in definitions like this it is
possible to *click* on any colored symbol to reach its definition.

By loading the program using `C-c C-l`, Agda verifies that `f` is
well typed and that its type is consistent with the one provided in
its signature. Once this is done, we can use again `C-c C-d` to
verify that `f` has type `ℕ -> ℕ`.

When defining functions, Agda provides an alternative, more
convenient notation with which argument and body of the function are
separated by the symbol `=` . For example, an equivalent way of
defining `f` is

```
f₁ : ℕ -> ℕ
f₁ x = x ^ 2 + 1
```

which can be read as "`f₁` applied to `x` is equal to `x ^ 2 +
1`". We have named this alternative definition of the function `f₁`
instead of `f` to avoid a *name clash*: there cannot be two
definitions with the same name in the same Agda file. Here and in
the following we will use indices whenever we need to provide
multiple versions of the same definition.

## Applying functions

Applying a function `M` to an argument `N` is achieved simply by
placing `M` and `N` next to each other, usually separated by one
space. For example, the expression `f 2` means the application of
`f` (defined above) to the natural number `2`. We can evaluate this
application by entering `C-c C-n f 2`, with which we obtain `5` as
result. The command `C-c C-n` asks Agda to *evaluate* (technically,
to *normalize*), the provided expression.

Agda is a strongly typed language, in the sense that it only
considers (and evaluates) terms that are **well typed** according to
a specific set of **typing rules**. We will not describe Agda's
typing rules in detail. For the time being, the following informal
statements explain when a function and an application are well
typed:

* If `M` is a term of type `B` under the assumption that `x` has
  type `A`, then `λ (x : A) -> M` is a term of type `A -> B`;
* If `M` is a term of type `A -> B` and `N` is a term of type `A`,
  then `M N` is a term of type `B`.

In order to limit the use of parentheses and improve readability, in
the following we will make extensive use of some (standard)
conventions concerning function definitions and applications:

* We will omit the type of an argument when it is unimportant or
  clear from the context.
* We will often collapse nested functions into one, so that e.g. `λ
  x y z -> M` stands for `λ x -> λ y -> λ z -> M`.
* We will assume that the body of a function extends as much as
  possible to the right. For example, `λ x y -> x y` stands for `λ x
  y -> (x y)` and not for `(λ x y -> x) y`.
* We will assume that application is **left associative**, so that
  `M₁ M₂ M₃` stands for `(M₁ M₂) M₃` and not for `M₁ (M₂ M₃)`.

We will introduce new terms in the following chapters. For the time
being, since we have imported the `Nat` module from the library, a
number of terms defined therein are also available. In particular:

* `zero` of type `ℕ` represents the natural number zero;
* `succ` of type `ℕ -> ℕ` is a function that, applied to a natural
  number, yields its successor.
* `_+_` of type `ℕ -> ℕ -> ℕ` is the function such that `_+_ M N`
  adds `M` and `N`. We often write this application in the usual
  infix notation `M + N`.
* `_^_` of type `ℕ -> ℕ -> ℕ` is the function such that `_^_ M N`
  computes `M` to the power `N`. We often write this application in
  the infix notation `M ^ N`.

The usual positional notation for natural numbers is also available,
so that `0` can be used as abbreviation for `zero`, `2` can be used
for abbreviation for `(succ (succ zero))` and `42` can be used for
abbreviation for 42 applications of `succ` to `zero`.

Finally, a note on **spacing** in Agda: unlike most programming
languages, Agda allows almost any character to be part of an
identifier. For example, `^` and `+` are plain Agda identifiers just
like `f` and `ℕ`. If we write `x^2` (without spaces around `^`),
Agda considers this as a single identifier (for which there is no
definition).

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
2. Define a function `poly₁` that, applied to a natural number $x$,
   yields $2x^2$.
3. Define a function `poly₂` that, applied to two natural numbers
   $x$ and $y$, yields $2(x^3 + y^2)$.
4. Which of the following terms are well typed? Use Agda to verify
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

-- EXERCISE 2

poly₂ : ℕ -> ℕ
poly₂ x = 2 * x ^ 2

poly₃ : ℕ -> ℕ -> ℕ
poly₃ x y = 2 * (x ^ 3 + y ^ 2)
```
{:.solution}
