---
fontsize: 12pt
papersize: a4
pagestyle: empty
margin-left: 1in
margin-right: 1in
header-includes: |
	\usepackage{a4wide}
	\usepackage{newunicodechar}
	\newunicodechar{ℕ}{\ensuremath{\mathnormal{\mathbb{N}}}}
---

# Static Analysis and Program Verification -- Exam

\thispagestyle{empty}

* You **cannot consult any teaching material** (Moodle page, lecture
  notes, etc.)
* You can **look at** and **import** any module from the Agda
  library used in the lectures.
* You can **define any auxiliary function** in addition to the
  requested results.
* You have **45 minutes** to complete the assignment.
* Be ready to **explain** any part of the code you submit.

## Definition

The following data type defines a predicate `Split` such that `Split
xs ys zs` holds if `xs` can be split into `ys` and `zs`.

``` agda
data Split {A : Set} : List A -> List A -> List A -> Set where
  split-[] : Split [] [] []
  split-l : {x : A} {xs ys zs : List A} -> Split xs ys zs ->
            Split (x :: xs) (x :: ys) zs
  split-r : {x : A} {xs ys zs : List A} -> Split xs ys zs ->
            Split (x :: xs) ys (x :: zs)
```

## Exercise 1 (5 points)

``` agda
split-comm : {A : Set} {xs ys zs : List A} -> Split xs ys zs ->
             Split xs zs ys
split-comm = ?
```

## Exercise 2 (5 points)

``` agda
split-refl : {A : Set} (xs : List A) -> Split xs [] xs
split-refl = ?
```

## Exercise 3 (5 points)

``` agda
split-++ : {A : Set} (xs ys : List A) -> Split (xs ++ ys) xs ys
split-++ = ?
```

## Exeercise 4 (15 points)

Define the function `sum` that computes the sum of the elements of a
list of natural numbers. Then, prove the following result:

``` agda
split-sum : {xs ys zs : List ℕ} -> Split xs ys zs ->
            sum xs == sum ys + sum zs
split-sum = ?
```
