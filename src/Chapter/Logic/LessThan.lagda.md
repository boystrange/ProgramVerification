---
title: Inequality
prev:  Chapter.Logic.Equality
---

```
module Chapter.Logic.LessThan where
```

In this section we define the non-strict inequality relation on
natural numbers and prove some of its fundamental properties.

## Imports

```
open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
```

## Non-strict inequality

We define non-strict inequality as an inductive family according to
the following rules.

                                      x <= y
    [le-zero] ------    [le-succ] --------------
              0 <= x              1 + x <= 1 + y

As we will see in a [later section](Chapter.Fun.Division.html), this
is not the only conceivable inference system that defines non-strict
inequality. However, it turns out to be a convenient one in most
situations.

```
infix 4 _<=_

data _<=_ : ℕ -> ℕ -> Set where
  le-zero : ∀{x : ℕ} -> 0 <= x
  le-succ : ∀{x y : ℕ} -> x <= y -> succ x <= succ y
```

The axiom `le-zero` proves that `0` is the least element, whereas
the rule `le-succ` builds a proof of `succ x <= succ y` from a proof
of `x <= y`. As an example, we can derive `2 <= 3` with two
applications of `le-succ` and one application of `le-zero`. In
general, there are as many applications of `le-succ` as the value of
the smaller number.

```
_ : 2 <= 3
_ = le-succ (le-succ le-zero)
```

## Correctness and completeness

Even though the definition of `<=` seems to make sense, one may
wonder whether it actually characterizes the non-strict inequality
on natural numbers. We can see that this is the case by showing that
`<=` is correct and complete with respect to another
characterization of such relation given in terms of addition.

```
_<=ₘ_ : ℕ -> ℕ -> Set
x <=ₘ y = ∃[ z ] x + z == y
```

According to this definition, `x` is not larger than `y` if there
exists some natural number `z` such that `x + z == y`. We can prove
that `<=` implies `<=ₘ` as follows.

```
le-correct : ∀{x y : ℕ} -> x <= y -> x <=ₘ y
le-correct le-zero = _ , refl
le-correct (le-succ le) with le-correct le
... | z , refl = z , refl
```

The idea is that the `z` in the definition of `<=ₘ` coincides with
the `y` found in the application of `le-zero`. We have used the
underscore since `refl` unifies `z` with `y` when `x` is `0`. For
every application of `le-succ` proving `succ x <= succ y` we
recursively find the `z` such that `x + z == y`, which is the same
`z` such that `succ x + z == succ y`. Note that we cannot simplify
this case to

    le-correct (le-succ le) = le-correct le

even though the result of `le-correct le` superficially appears to
be the same result of `le-correct (le-succ le)`, the reason being
that the two `refl`s prove different equalities (`x + z == y` in the
former case and `succ x + z == succ y` in the latter). In fact,
(some of) the implicit arguments supplied to the two occurrences of
`refl` differ.

We can also show that `<=` is complete with respect to `<=ₘ`.

```
le-complete : ∀{x y : ℕ} -> x <=ₘ y -> x <= y
le-complete (z , refl) = lemma
  where
    lemma : ∀{x y : ℕ} -> x <= x + y
    lemma {zero}   = le-zero
    lemma {succ _} = le-succ lemma
```

By performing case analysis on the proof of `x <=ₘ y` we unify `y`
with `x + z`, so our goal turns into providing a proof of `x <= x +
z`. This is done by means of the local `lemma`.

## Inequality is a total order

Here we prove that `<=` is a **total order** on the natural
numbers. We begin by proving **reflexivity**.

```
le-refl : ∀{x : ℕ} -> x <= x
le-refl {zero}   = le-zero
le-refl {succ x} = le-succ le-refl
```

If two numbers are mutually related by `<=`, then they must be
equal. This property is called **antisymmetry** and is proved below.

```
le-antisymm : ∀{x y : ℕ} -> x <= y -> y <= x -> x == y
le-antisymm le-zero     le-zero     = refl
le-antisymm (le-succ p) (le-succ q) = cong succ (le-antisymm p q)
```

It is interesting to observe that the case analysis only considers
those combinations in which `x <= y` and `y <= x` are proved by
means of the same constructors. Indeed, when `x <= y` is proved by
`le-zero`, then `x` must be `0` and the only proof of `y <= x` must
have been obtained with `le-zero` as well. Similarly, when `x <= y`
is proved by `le-succ` then `y` must have the form `succ z` for some
`z`, hence the proof of `y <= x` must have been obtained by an
application of `le-succ` too.

Concerning **transitivity**, it is convenient to perform case
analysis on the proofs of `x <= y` and `y <= z`. Note that, when the
former relation is proved by `le-succ`, the second relation can only
be proved by `le-succ` because `y` has the form `succ z`.

```
le-trans : ∀{x y z : ℕ} -> x <= y -> y <= z -> x <= z
le-trans le-zero     q           = le-zero
le-trans (le-succ p) (le-succ q) = le-succ (le-trans p q)
```

To conclude the proof that `<=` is a total order we have to show
that any two natural numbers `x` and `y` are related in one way or
another. This follows from a straightforward cases analysis on them.

```
le-total : ∀(x y : ℕ) -> x <= y ∨ y <= x
le-total zero     _    = inl le-zero
le-total (succ _) zero = inr le-zero
le-total (succ x) (succ y) =
  ∨-elim (inl ∘ le-succ) (inr ∘ le-succ) (le-total x y)
```

## Exercises

1. Show that `<=` is decidable, namely prove the theorem `_<=?_ : ∀(x
   y : ℕ) -> Decidable (x <= y)`.
2. Define `min : ℕ -> ℕ -> ℕ` and `max : ℕ -> ℕ -> ℕ` and prove the theorems
   `le-min : ∀{x y z : ℕ} -> x <= y -> x <= z -> x <= min y z` and `le-max : ∀{x y z : ℕ} -> x <= z -> y <= z -> max x y <= z`.
3. Strict inequality `x < y` can be defined to be the same as `succ x
   <= y`. Prove that this relation is transitive and irreflexive.

```
-- EXERCISE 1

_<=?_ : ∀(x y : ℕ) -> Decidable (x <= y)
zero   <=? y    = inr le-zero
succ x <=? zero = inl λ ()
succ x <=? succ y with x <=? y
... | inl gt = inl λ { (le-succ le) -> gt le }
... | inr le = inr (le-succ le)

_<_ : ℕ -> ℕ -> Set
x < y = succ x <= y

-- EXERCISE 2

-- ...

-- EXERCISE 3

lt-irrefl : ∀{x : ℕ} -> ¬ (x < x)
lt-irrefl {succ zero}     (le-succ ())
lt-irrefl {succ (succ _)} (le-succ (le-succ lt)) = lt-irrefl lt

-- ...
```
{:.solution}
