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
* You have **90 minutes** to complete the assignment.
* Be ready to **explain** any part of the code you submit.

## Assignment

Consider the following definition.

``` agda
pow : {A : Set} -> List A -> ℕ -> List A
pow _  0        = []
pow xs (succ n) = xs ++ pow xs n
```

Solve the following exercises.

1. Prove that if `xs ++ ys == []` then `xs == [] ∧ ys == []` for
   every `xs` and `ys`.
2. Prove that `pow xs n == []` implies `n == 0 ∨ xs == []` for every
   `xs` and `n`. Hint: use the solution of the previous exerecise.
3. Prove that `length (pow xs n) == n * length xs` for every `xs`
   and `n`.
4. Prove that `xs ++ pow xs n == pow xs n ++ xs` for every `xs` and
   `n`.
5. Prove that `pow (reverse xs) n == reverse (pow xs n)` for every
   `xs` and `n`. Hints: use the solution of the previous exercise as
   well as `reverse-++` from the library.
