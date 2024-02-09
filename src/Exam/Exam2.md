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
data Merge {A : Set} : List A -> List A -> List A -> Set where
  merge-[] : Merge [] [] []
  merge-l  : {x : A} {xs ys zs : List A} -> Merge xs ys zs ->
             Merge (x :: xs) ys (x :: zs)
  merge-r  : {y : A} {xs ys zs : List A} -> Merge xs ys zs ->
             Merge xs (y :: ys) (y :: zs)
```

Note that a proof of `Merge xs ys zs` represents the fact that `zs`
is a list obtained by *merging* `xs` and `ys`.

Solve the following exercises.

1. Prove that the list `0 :: 1 :: 2 :: 3 :: 5 :: []` is the merge of
   `1 :: 3 :: 5 :: []` and `0 :: 2 :: []`.
2. Prove that `Merge xs ys []` implies `xs == [] ∧ ys == []`.
3. Prove that `Merge xs ys [ x ]` implies `xs == [] ∨ ys == []`
   using the solution of the previous exercise.
4. Prove that `Merge xs ys zs` implies `Merge ys xs zs`.
5. Prove that `Merge xs ys zs` implies `length zs == length xs + length ys`.
6. Prove that `Merge xs ys zs` implies `zs # xs ++ ys`.
