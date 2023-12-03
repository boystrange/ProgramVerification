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

Consider the following definitions.

``` agda
take : ∀{A : Set} -> ℕ -> List A -> List A
take zero     xs        = []
take (succ n) []        = []
take (succ n) (x :: xs) = x :: take n xs
```

Solve the following exercises.

1. State and prove the property that the length of `take n xs` is
   always smaller than (`<=`) the length of `xs`.
2. Define a predicate `Prefix` such that `Prefix xs ys` holds if the
   list `xs` is a **prefix** of the list `ys` (that is, `ys` begins
   with `xs` and is possibly followed by something else). Make sure
   that `Prefix` can be used on lists of any type.
3. State and prove the property that `take n xs` is always a prefix
   of `xs`.
4. State and prove the property that, for every natural number `n`
   and list `xs`, there exists a list `ys` such that `take n xs ++ ys == xs`.
5. Prove that `::` (the constructor of lists) is injective, namely
   that if `x :: xs == y :: ys` then `x == y` and `xs == ys`.
6. Prove the theorem `∀{A B : Set} -> A ∧ B -> ¬ (¬ A ∨ ¬ B)`.
