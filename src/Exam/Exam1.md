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

Consider the following definition.

``` agda
data Chop {A : Set} : List A -> List A -> Set where
  chop-last : {x : A} -> Chop (x :: []) []
  chop-next : {x : A} {xs ys : List A} -> Chop xs ys ->
              Chop (x :: xs) (x :: ys)
```

Solve the following exercises.

1. Prove `Chop (0 :: 1 :: 2 :: []) (0 :: 1 :: [])`.
2. Prove that `Chop xs ys` implies `length xs == succ (length ys)`.
3. Prove that `Chop` is not symmetric, namely that `Chop xs ys`
   implies `¬ Chop ys xs`.
4. Using the previous result, prove that `Chop` is not reflexive,
   namely that `Chop xs xs` does **not** hold for every `xs`.
5. Prove that `Chop xs ys` implies `Chop (zs ++ xs) (zs ++ ys)` for
   every `zs`.
