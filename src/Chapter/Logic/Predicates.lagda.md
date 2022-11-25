---
title: Defining predicates
prev:  Chapter.Logic.Existential
next:  Chapter.Logic.Equality
---

```
module Chapter.Logic.Predicates where
```

In this chapter we study and compare several techniques with which
it is possible to define *predicates* in Agda.

## Imports

```
open import Library.Fun
open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
```

## The half of a natural number

Consider the following function which computes the (truncated) half
of a natural number:

```
half : ℕ -> ℕ
half zero            = zero
half (succ zero)     = zero
half (succ (succ x)) = succ (half x)
```

We would like to prove a theorem asserting that, by doubling the
half of an even natural number `x`, we obtain the original number
`x`. In order to do so, we have to teach Agda what it means for a
natural number to be even. As we will see, there are several ways of
doing this. For each way, we will show how to prove the desired
result discussing pros and cons of the approach.

## Being even, programmatically

The first, and possibly most obvious, way of defining "evenness" is
by means of a recursive function that returns either `true` or
`false`. We call this the "programmer's" way of defining evenness,
since it is the approach that any (functional) programmer would
choose in the first place.

```
Even-p : ℕ -> Bool
Even-p zero            = true
Even-p (succ zero)     = false
Even-p (succ (succ x)) = Even-p x
```

Notice that `Even-p x` is a *term* of type `Bool`. So, in order to
use `Even-p` as a predicate, we have to compare the result of
`Even-p x` to `true` using equality. We can thus formulate our
theorem as follows.

```
theorem-p : ∀{x : ℕ} (ev : Even-p x == true) -> x == half x * 2
theorem-p {zero}          refl = refl
theorem-p {succ (succ x)} ev   = cong (succ ∘ succ) (theorem-p ev)
```

We are forced to perform case analysis on the (implicit) argument
`x`, since the proof `ev` that `x` is an even number (which must
have the form `refl` for this is the only normal proof of an
equality proof) bears no structure that helps us proving the
theorem. Interestingly, Agda does not propose an equation for the
case `succ zero`. This happens because `Even-p 1` yields `false`,
which is certainly different from `true`, so Agda realizes that this
case is impossible.

## Being even, mathematically

A mathematician asked to define evenness could possibly say that a
natural number `x` is even if it is the double of another natural
number `y`. Being the double of some natural number `y` is a
property that we can specify in Agda using an existential type. So,
we can define this notion of evenness as follows.

```
Even-m : ℕ -> Set
Even-m x = ∃[ y ] x == y * 2
```

Unlike `Even-p`, which returns a *term* (of type `Bool`), `Even-m`
returns a *type* (of type `Set`). This type is inhabited by pairs of
the form `(y , p)` where `y` is some natural number and `p` is a
proof that `x` is the double of `y`. For example, we can prove that
`4` is even as follows.

```
_ : Even-m 4
_ = 2 , refl
```

Analogously we can show that `1` is *not* even by proving a
contradiction if we assume that it is even.

```
_ : ¬ Even-m 1
_ = λ { (zero , ()) ; (succ _ , ()) }
```

When proving that doubling the half of an even number `x` yields
`x`, we can perform case analysis on the proof that `x` is even
obtaining some witness `y` whose double is known to be `x`. We can
conclude if we are able to show that halving a doubled number `y`
yields `y`. For this, we need to prove an auxiliary lemma, which we
locally define within `theorem-m` after the keyword `where`.

```
theorem-m : ∀{x : ℕ} (ev : Even-m x) -> x == half x * 2
theorem-m (y , refl) = cong (_* 2) (lem y)
  where
    lem : (x : ℕ) -> x == half (x * 2)
    lem zero     = refl
    lem (succ x) = cong succ (lem x)
```

## Type-level computations

In the previous approach we have defined a function `Even-m` that,
applied to a natural number `x`, yields the type of proofs that `x`
is even. We can apply the same principle to write an alternative
version of `Even-p` in which the result is a type instead of a
boolean value. In this case, the returned type is `⊤` when we
realize that `x` is even and `⊥` otherwise. This approach is
sometimes referred to as making use of *type-level computations*
because it computes a type (`Even-r x`) from a term `x` (technically
speaking, also `Even-m` is defined in this way).

```
Even-r : ℕ -> Set
Even-r zero            = ⊤
Even-r (succ zero)     = ⊥
Even-r (succ (succ x)) = Even-r x
```

Compared to `Even-p`, the advantage of `Even-r` is that it yields a
type, so it is not necessary to use equality to turn `Even-r x` into
a type. However, just like when using `Even-p`, the proof of `Even-r
x` is simply `<>`, so inspecting the proof of `Even-r x` does not
reveal anything useful about `x` and we are forced to perform case
analysis on `x` to complete our theorem.

```
theorem-r : ∀{x : ℕ} (ev : Even-r x) -> x == half x * 2
theorem-r {zero}          <> = refl
theorem-r {succ (succ x)} ev = cong (succ ∘ succ) (theorem-r ev)
```

Also in this approach Agda does not propose a case for `succ zero`
when we perform case analysis on `x`. The reason is that, in this
case, `ev` has type `Even-r 1` which is `⊥`. Agda figures that no
such term exists (`⊥` is not inhabited by any term).

## Being even as an inference system

The final point of view we consider is motivated by the observation
that the set of *even natural numbers* is the smallest set $X$ such
that:

* $0 \in X$, and
* if $x \in X$, then $2 + x \in X$ as well.

In other words, we can characterize the whole set of even numbers as
those satisfying the predicate `Even x`, where `Even` is inductively
defined by the following inference rules.

                                         Even x
    [even-zero] ------    [even-succ] ------------
                Even 0                Even (2 + x)

The axiom `[even-zero]` asserts that `0` is an even number. The rule
`[even-succ]` asserts that `2 + x` is even whenever `x` is. We can
define this inference system as an inductive data type such that

* the name of the data type (`Even-i`) corresponds to the name of
  the predicate (`Even`) we are defining;
* the constructors of the data type correspond to axioms/rules in
  the inference system defining the predicate;
* terms of the data type correspond to derivations in this inference system.

Note that the evenness predicate `Even-i x` we are defining in this
way depends on the natural number `x` that is claimed to be even. We
cannot express this dependency merely using a parameter of the data
type, since parameters are supposed to be the same across the whole
data type definition whereas the value of `x` varies (e.g., it is
`0` in `[even-zero]` and it is `x` and `2 + x` in
`[even-succ]`). For this reason, we define an **indexed data type**
(also known as **inductive family**), which differs from a plain (or
parametric) data type as it contains one or more **indexes**. In our
case, a single index of type `ℕ` suffices.

```
data Even-i : ℕ -> Set where
  even-zero : Even-i 0
  even-succ : {x : ℕ} -> Even-i x -> Even-i (2 + x)
```

The type of `Even-i` is `ℕ -> Set` and not just `Set`, namely
`Even-i` is a function that, applied to some natural number `x`,
yields a type. The `x` is the index of `Even-i`. There are two ways
of building terms of type `Even-i x`. One is through the constructor
`even-zero`. In this case `x` must be `0`. The other is through the
constructor `even-succ` applied to a term of type `Even-i x`, which
yields a term of type `Even-i (2 + x)`.

As an example, we can prove that `4` is even and that `1` is not as
follows.

```
_ : Even-i 4
_ = even-succ (even-succ even-zero)

_ : ¬ Even-i 1
_ = λ ()
```

When we prove our theorem using `Even-i` we can perform a case
analysis directly on `Even-i x`, which contains all the structure we
need.

```
theorem-i : ∀{x : ℕ} (ev : Even-i x) -> x == half x * 2
theorem-i even-zero      = refl
theorem-i (even-succ ev) = cong (succ ∘ succ) (theorem-i ev)
```

## Exercises

1. Prove that all the provided definitions of evenness are
   equivalent, for instance that `Even-p x == true` implies `Even-r
   x`, that `Even-r x` implies `Even-i x`, that `Even-i x` implies
   `Even-m x` and that `Even-m x` implies `Even-p x == true`.
2. Prove that `x == 1 + x /2 * 2` when `¬ Even-i x` holds.
3. Prove that `Even-i` is decidable, namely the theorem `∀(x : ℕ) ->
   Decidable (Even-i x)`.
4. Define an indexed data type `Odd-i` analogous to `Even-i` but
   such that `Odd-i x` holds if and only if `x` is odd. Prove that
   `5` is odd and `2` is not.
5. Prove that `Even-i x ∨ Odd-i x` holds and that `Even-i x ∧ Odd-i
   x` does not for every `x`.
6. Prove that `Odd-i x` implies `x == 1 + x/2 * 2` without using
   recursion, but reusing the results of exercises 2 and 4.


```
-- EXERCISE 1

p=>r : ∀(x : ℕ) -> Even-p x == true -> Even-r x
p=>r zero            eq = <>
p=>r (succ (succ x)) eq = p=>r x eq

r=>i : ∀(x : ℕ) -> Even-r x -> Even-i x
r=>i zero            ev = even-zero
r=>i (succ (succ x)) ev = even-succ (r=>i x ev)

i=>m : ∀{x : ℕ} -> Even-i x -> Even-m x
i=>m even-zero = 0 , refl
i=>m (even-succ ev) with i=>m ev
... | y , refl = succ y , refl

m=>p : ∀{x : ℕ} -> Even-m x -> Even-p x == true
m=>p (y , refl) = lem y
  where
    lem : ∀(y : ℕ) -> Even-p (y * 2) == true
    lem zero     = refl
    lem (succ y) = lem y

-- EXERCISE 2

not-even : ∀(x : ℕ) -> ¬ Even-i x -> x == 1 + half x * 2
not-even zero            nev = ex-falso (nev even-zero)
not-even (succ zero)     nev = refl
not-even (succ (succ x)) nev = cong (succ ∘ succ) (not-even x (lem x nev))
  where
    lem : ∀(x : ℕ) -> ¬ Even-i (2 + x) -> ¬ Even-i x
    lem x nev ev = nev (even-succ ev)

-- EXERCISE 3

Even? : ∀(x : ℕ) -> Decidable (Even-i x)
Even? zero            = inr even-zero
Even? (succ zero)     = inl λ ()
Even? (succ (succ x)) with Even? x
... | inr ev  = inr (even-succ ev)
... | inl nev = inl λ { (even-succ ev) → nev ev }

-- EXERCISE 4

data Odd-i : ℕ -> Set where
  odd-one  : Odd-i 1
  odd-succ : ∀{x : ℕ} -> Odd-i x -> Odd-i (2 + x)

_ : Odd-i 5
_ = odd-succ (odd-succ odd-one)

_ : ¬ Odd-i 2
_ = λ { (odd-succ ()) }

-- EXERCISE 5

even-or-odd : ∀(x : ℕ) -> Even-i x ∨ Odd-i x
even-or-odd zero            = inl even-zero
even-or-odd (succ zero)     = inr odd-one
even-or-odd (succ (succ x)) with even-or-odd x
... | inl ev = inl (even-succ ev)
... | inr od = inr (odd-succ od)

even-and-odd : ∀(x : ℕ) -> ¬ (Even-i x ∧ Odd-i x)
even-and-odd zero            (_  , ())
even-and-odd (succ zero)     (() , _ )
even-and-odd (succ (succ x)) (even-succ ev , odd-succ od) = even-and-odd x (ev , od)

-- EXERCISE 6

odd : ∀{x : ℕ} -> Odd-i x -> x == 1 + half x * 2
odd {x} od = not-even x (contraposition (_, od) (even-and-odd x))
```
{:.solution}
