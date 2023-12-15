---
title: Static Analysis and Program Verification -- Exam
fontfamily: palatino
fontsize: 12pt
papersize: a4
pagestyle: empty
margin-left: 1in
margin-right: 1in
header-includes: |
	\usepackage[utf8]{inputenc}
	\usepackage{newunicodechar}
	\newunicodechar{∀}{\ensuremath\forall}
	\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
	\newunicodechar{∧}{\ensuremath{\wedge}}
	\newunicodechar{∨}{\ensuremath{\vee}}
	\newunicodechar{∈}{\ensuremath{\in}}
---

\thispagestyle{empty}

## Rules

* While working at your assignment you **cannot consult any teaching
  material** (Moodle page, lecture notes, recordings, etc.)
* You can **look at** and **import** any module from the Agda
  library used in the lectures.
* You can **define any auxiliary function** that may be useful for
  completing the assignment.
* You have **90 minutes** to complete the assignment.
* Be ready to **explain** any part of the code you submit.

## Assignment

Consider the following definition of the "belongs to" predicate `∈`.

``` agda
infix 4 _∈_

data _∈_ {A : Set} (x : A) : List A -> Set where
  in-head : {xs : List A} -> x ∈ (x :: xs)
  in-tail : {y : A} {xs : List A} -> x ∈ xs -> x ∈ (y :: xs)
```

Solve the following exercises. Type `\in` to enter the `∈` symbol.

1. Prove that the natural number `2` belongs to the list `0 :: 1 :: 2 :: 3 :: 4 :: []`.
2. Prove that `x` belongs to any list of the form `xs ++ x :: ys`.
3. Prove that `x ∈ xs` implies `1 <= length xs`.
4. Prove `∀{A : Set} (xs : List A) -> (∀(x : A) -> ¬ (x ∈ xs)) -> xs == []`.
5. Prove that if `x` belongs to `xs` and `ys` is a permutation of
   `xs`, then `x` belongs to `ys`.
6. Prove that `x ∈ xs ++ ys` implies `x ∈ xs ∨ x ∈ ys`.
