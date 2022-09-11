---
title: Equality
prev:  Chapter.Logic.Predicates
next:  Chapter.Logic.LessThan
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
-->

```
module Chapter.Logic.Equality where
```

We have now all the necessary ingredients to understand how
propositional equality is defined in Agda.

## Imports

```
open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Logic
```

## Propositional equality

Propositional equality is nothing but an inductive family with an
implicit parameter `A` (the type of the terms being compared), a
parameter `x` (the leftmost term being compared) and an index (the
rightmost term being compared).

```
infix 4 _==_

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x
```

As we can see from its definition, there is just one way of proving
an equality `x == y`, namely by using the constructor `refl`, which
imposes the two compared terms to be the same `x`. The name of this
constructor is intended to suggest that we are using the
*reflexivity* property of equality: every term is equal to
itself. In general, since Agda considers two terms to be "the same"
if they have the same normal form, we can use `refl` to construct
equality proofs for any two terms `x` and `y` that have the same
normal form. We have already seen a few examples of this when
proving [properties of boolean values](Chapter.Intro.BoolProperties.html) and when introducing
[natural numbers](Chapter.Intro.NaturalNumbers.html).

```
_ : not true == false
_ = refl

_ : 1 + 2 == 3
_ = refl
```

## Symmetry and transitivity

At first, it may be surprising that there are no ways of proving the
equality of two terms `x` and `y` other than reflexivity. After all,
we expect equality to be an equivalence relation, hence it should
also be *symmetric* and *transitive*. As it turns out, symmetry and
transitivity of equality can be proved as consequences of
reflexivity. Their proofs makes use of **dot patterns**, a feature
of Agda that we haven't seen so far.

Let us start with symmetry. The property that we want to prove is
stated as follows.

```
symm : ∀{A : Set} {x y : A} -> x == y -> y == x
symm {_} {x} {y} eq = {!!}
```

For the sake of illustration, we have given names to the implicit
arguments `x` and `y`, whereas we have kept `A` unnamed as it plays
no interesting role in the proof. By inspecting the hole, we see
that we have to provide a proof of `y == x` in a context where we
have two elements `x` and `y` of type `A` and a term `eq` of type `x
== y`. Given the current situation, there isn't much we can do
except realize that equality is an inductively defined data type. As
such, we can perform case analysis on `eq`.

```
symm₁ : ∀{A : Set} {x y : A} -> x == y -> y == x
symm₁ {_} {x} {.x} refl = {!!}
```

As expected, the `eq` argument has turned into `refl`. However, case
analysis has also changed the pattern for the third implicit
argument `y`, which has turned into `.x`. This pattern means that
the third (implicit) argument of `symm` is not arbitrary, but it
must be the same as the second (implicit) argument `x`. The reason
is that the only way the constructor `refl` can be used as evidence
for the equality `x == y` is when `x` and `y` are the same (up to
Agda's definitional equality).

This case analysis has another interesting effect on the context of
the hole that we are supposed to fill. By inspecting the hole we see
that the variable `y` is no longer present, since `x` and `y` have
been *unified*. As a consequence, the type of the hole has changed
from `y == x` to `x == x`. This means that we are now able to
complete the proof, since `refl` will provide evidence of the fact
that `x` is equal to itself.

```
symm₂ : ∀{A : Set} {x y : A} -> x == y -> y == x
symm₂ {_} {x} {.x} refl = refl
```

The proof that equality is transitive follows a similar pattern.

```
trans : ∀{A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans eq1 eq2 = {!!}
```

By performing case analysis on `eq1` and `eq2` we effectively unify
the three (implicit) arguments `x`, `y` and `z`, so that we end up
with having to prove `x == x`, which can be done by reflexivity.

```
trans₁ : ∀{A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans₁ refl refl = refl
```

## Congruence and substitution

In the chapter on [natural numbers](Chapter.Intro.NaturalNumbers.html) we have used the congruence
property of function application, namely the property that, if `x ==
y`, then `f x == f y`. We can now see how this theorem is proved.

```
cong : ∀{A B : Set} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong _ refl = refl
```

Once again we rely on case analysis to force the unification of `x`
and `y`, thereby turning congruence into another case of
reflexivity. Another principle related to equality is
*substitution*, asserting that if `x == y` and we know that `x`
satisfies some predicate `P`, then `y` also satisfies the same
predicate.

```
subst : ∀{A : Set} (P : A -> Set) {x y : A} -> x == y -> P x -> P y
subst _ refl p = p
```

## Equational reasoning

TODO

## Homework

1. Prove that `succ` is injective, namely the theorem
   `succ-injective : ∀{x y : ℕ} -> succ x == succ y -> x == y`.
2. Define the relation `_!=_` as the negation of equality.
   Prove that `zero` is different from any other natural number, namely
   the theorem `zero-succ : ∀{x : ℕ} -> zero != succ x`
3. Prove the theorem `ne-ne : ∀{x y : ℕ} -> succ x != succ y -> x != y`.
4. Prove that `_::_` is injective, namely the theorem
   `::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys ->
   x == y ∧ xs == ys`.
5. Prove a version of `cong` for two-argument functions, namely the
   theorem `cong2 : ∀{A B C : Set} (f : A -> B -> C) {x y : A} {u v :
   B} -> x == y -> u == v -> f x u == f y v`

```
-- EXERCISE 1

succ-injective : ∀{x y : ℕ} -> succ x == succ y -> x == y
succ-injective refl = refl

-- EXERCISE 2

_!=_ : ∀{A : Set} -> A -> A -> Set
x != y = ¬ (x == y)

zero-succ : ∀{x : ℕ} -> zero != succ x
zero-succ ()

-- EXERCISE 3

ne-ne : ∀{x y : ℕ} -> succ x != succ y -> x != y
ne-ne neq refl = neq refl

-- EXERCISE 4

::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys -> x == y ∧ xs == ys
::-injective refl = refl , refl

-- EXERCISE 5

cong2 : ∀{A B C : Set} (f : A -> B -> C) {x y : A} {u v : B} -> x == y -> u == v -> f x u == f y v
cong2 _ refl refl = refl
```
{:.solution}
