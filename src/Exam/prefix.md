---
title: Static Analysis and Program Verification -- Exam
fontsize: 12pt
papersize: a4
pagestyle: empty
margin-left: 1in
margin-right: 1in
---

\thispagestyle{empty}

## Rules

* While working at your assignment you **cannot consult any teaching
  material** (Moodle page, lecture notes, recordings, etc.)
* You can **look at** and **import** any module from the Agda
  library used in the lectures.
* You can **define any auxiliary function** that may be useful for
  completing the assignment.
* You have **45 minutes** to complete the assignment.
* Be ready to **explain** any part of the code you submit.

## Assignment

Define a predicate `Prefix` such that `Prefix xs ys` holds whenever
the list `xs` is a **prefix** of the list `ys`. Prove the following
properties:

* `Prefix` is reflexive;
* `Prefix` is transitive;
* `Prefix` is antisymmetric, namely if both `Prefix xs ys` and
  `Prefix ys xs` hold, then `xs == ys`;
* if `Prefix xs ys` holds, then the length of `xs` is less than or
  equal to the length of `ys`.
