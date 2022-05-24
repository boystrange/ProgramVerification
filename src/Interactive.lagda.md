---
title: Interactive Program Development
---

<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}

module Interactive where

postulate A B C : Set
```
-->


-- Interactive development, CTRL-C, CTRL-R

```text
  id₄ : A -> A
  id₄ = {!!}
```

<!--
```agda
module X2 where
```
```agda
  id₄ : A -> A
  id₄ = {!!}
```
-->

It is likely that Emacs will only show a highlighted hole *without*
the symbols `!!` inside it. Also, you may see a number next to the
hole. This number is just an identifier for the hole. The Emacs
frame will split and a bottom part will appear

```text
?0 : A -> A
```

indicating that the hole identified by the number 0 should be filled
with a term of type `A -> A`.

`CTRL-C` followed by `CTRL-F` to automatically move the cursor to
the next hole, and `CTRL-C` followed by `CTRL-B` to automatically
move the cursor to the previous hole (these commands are easy to
remember noting that `F` stands for Forward and `B` stands for
Backward).

Once the cursor is inside a hole, we have two ways to proceed. One
is to explicitly **give** an expression to fill the hole. This can
be achieved by entering the expression, e.g. `λ x -> x`, and then
typing `CTRL-C` followed by `CTRL-SPACE`.  If the given term has the
correct type, Agda closes the hole.

```agda
module X3 where
  id₄ : A -> A
  id₄ = {! λ x -> x!}
```

Alternatively, it is possible to ask Agda for help by typing
`CTRL-C` followed by `CTRL-R`, where `R` stands for Refine. Agda
will inspect the type of the hole and will try to come up with a
term (possibly containing more holes) that is compatible with that
type.

In the particular case of `id₄`, by asking Agda to refine the hole
we obtain

```agda
id₄ : A -> A
id₄ = λ x -> {!!}
```

Beware: not always Agda refines the hole in the intended way
