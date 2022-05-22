---
title:   Test slides
---

# Introduction

## This is a test argument

Below this text there is some hidden Agda code

<!--
```agda
open import Type
open import Equality
```
-->

```agda
data ℕ : Type where
  zero : ℕ
  succ : ℕ -> ℕ
```

```agda
five : ℕ
five = succ (succ (succ (succ (succ zero))))
```

```agda
_+_ : ℕ -> ℕ -> ℕ
zero   + y = y
succ x + y = succ (x + y)

infixl 6 _+_
```

```agda
+-associative : (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-associative zero     y z = refl
+-associative (succ x) y z = context succ (+-associative x y z)

+-zero : ∀(x : ℕ) -> x == x + zero
+-zero zero = refl
+-zero (succ x) = context succ (+-zero x)

+-succ : ∀(x y : ℕ) -> succ (x + y) == x + succ y
+-succ zero y = refl
+-succ (succ x) y = context succ (+-succ x y)

+-commutative : (x y : ℕ) -> x + y == y + x
+-commutative zero y = +-zero y
+-commutative (succ x) y =
  begin
    succ x + y   ==⟨⟩
    succ (x + y) ==⟨ context succ (+-commutative x y) ⟩
    succ (y + x) ==⟨ +-succ y x ⟩
    y + succ x
  end
```

No longer display?

$$
  \int_0^\infty x
$$

In this course we're going to introduce **Agda**, which is at the
same time:

* A dependently-typed functional programming language
* A proof assistant, that is a tool that helps users proving theorems

We will use Agda to show how it is possible to formally verify
programs. We will start proving facts about functional programs, and
then show how Agda can be used to prove facts also about imperative
programs involving **mutable state**.

Lecture notes are provided in the form of "dense slides", which
intermix prose, Agda code and mathematical formulas. This is an
example of dense slide, which includes a row with two same-width
columns. Here are examples of _emphasized text_, **bold text** and
`inline code`.

## Second argument

## Exercises
