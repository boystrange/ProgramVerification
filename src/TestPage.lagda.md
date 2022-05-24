---
title: Test page
---

## This is a test argument

Below this text there is some hidden Agda code

<!--
```agda
open import Equality
open import Nat
```
-->

```agda
five : ℕ
five = succ (succ (succ (succ (succ zero))))
```

## Interactive programming

Use `?` to denote unknown terms, use `CTRL-C` followed by `CTRL-R`
to refine a hole.

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
interleave prose, Agda code and mathematical formulas. This is an
example of dense slide, which includes a row with two same-width
columns. Here are examples of _emphasized text_, **bold text** and
`inline code`.

## Second argument

```agda
_ : 2 == succ (succ zero)
_ = begin
      2 ==⟨⟩
      succ (succ zero) ==⟨⟩
      2 ==⟨⟩
      succ 1
    end
```

## Exercises
