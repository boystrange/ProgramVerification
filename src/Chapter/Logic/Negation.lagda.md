---
title: Negation and decidability
prev:  Chapter.Logic.Connectives
next:  Chapter.Logic.Existential
---

```
module Chapter.Logic.Negation where
```

## Imports

```
open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Fun
open import Library.Equality
open import Chapter.Logic.Connectives
```

## Constructive negation

In constructive logic, the `⊥` data type has a fundamental role
since it allows us to define negation. Showing that the *negation*
of a proposition `A` holds amounts to showing that a proof of `A`
can be turned into a proof of `⊥`.

```
¬_ : Set -> Set
¬_ A = A -> ⊥
```

We will make a rather extensive use of negation in the following
chapters. For the time being, we prove a few laws related to
negation. The first one is **contradiction**, namely the fact that
if we have both a proof of `A` and a proof of `¬ A` then we can
derive a proof of `⊥`. Recalling that the negation of `A` is defined
as a function that turns a proof of `A` into a proof of `⊥`, we see
that contradiction simply amounts to function application.

```
contradiction : ∀{A : Set} -> A -> ¬ A -> ⊥
contradiction p ¬p = ¬p p
```

Recalling that in Agda the type `¬ A` is *defined* to be the same as
the type `A -> ⊥`, the type of `contradiction` can also be written
as `∀{A : Set} -> A -> ¬ ¬ A`. This is one of the so-called "double
negation" laws.

```
double-negation : ∀{A : Set} -> A -> ¬ ¬ A
double-negation = contradiction
```

In classical logic, the inverse implication `¬ ¬ A -> A` is also
assumed to be true. However, this implication is not provable in
constructive logic (it is instructive to **attempt** proving this
property).

Another interesting law concerning negation is **contraposition**,
asserting that if `A` implies `B`, then `¬ B` implies `¬ A`.

```
contrapositive : ∀{A B : Set} -> (A -> B) -> ¬ B -> ¬ A
contrapositive f p q = p (f q)
```

Observe that we define `contrapositive` as a function with three
arguments `f`, `p` and `q`, while its type appears to have only two
arguments, one of type `A -> B` (that would be `f`) and the other of
type `¬ B` (that would be `p`). However, the type `¬ A` is actually
the type `A -> ⊥`, so `contrapositive` can be seen as also having a
third argument of type `A`, that would be `q`.

Using `contrapositive` and `double-negation` we can prove that
*triple* negation implies *single* negation.

```
triple-negation : ∀{A : Set} -> ¬ ¬ ¬ A -> ¬ A
triple-negation = contrapositive double-negation
```

## Decidability

In classical logic it is common to assume the validity of the
*excluded middle* principle, namely that `¬ A ∨ A` is true for every
proposition `A`. As we know from the [previous
chapter](Chapter.Logic.Connectives.html), in constructive logic, a
proof of a disjunction `¬ A ∨ A` embeds either a proof of `¬ A` or a
proof of `A`, hence it may very well be the case that we are unable
to prove `¬ A ∨ A` if we cannot find either a proof of `¬ A` or a
proof of `A`. The propositions for which we are able to prove `¬ A ∨
A` are said to be **decidable**.

```
Decidable : Set -> Set
Decidable A = ¬ A ∨ A
```

As an example of decidable property, consider the problem of
determining whether two boolean values are equal or not.  This can
be shown by considering all the possible cases, which are finite.

```
Bool-eq-decidable : ∀(x y : Bool) -> Decidable (x == y)
Bool-eq-decidable true  true  = inr refl
Bool-eq-decidable true  false = inl λ ()
Bool-eq-decidable false true  = inl λ ()
Bool-eq-decidable false false = inr refl
```

Note that we use the constructor `inr` ("inject right") for
representing a positive answer to the question "is `x` equal to
`y`?" and `inl` ("inject left") for representing a negative answer.

<!--

For readability purposes, it may be appropriate to give
these constructors more evocative names, such as `yes` and `no`. We
can do so (without defining an *ad hoc* `Decidable` data type) by
means of **pattern synonyms**.

```
pattern yes x = inr x
pattern no  x = inl x
```

With these declarations, we may write `Bool-eq-decidable` as follows.

```
Bool-eq-decidable₁ : ∀(x y : Bool) -> Decidable (x == y)
Bool-eq-decidable₁ true  true  = yes refl
Bool-eq-decidable₁ true  false = no λ ()
Bool-eq-decidable₁ false true  = no λ ()
Bool-eq-decidable₁ false false = yes refl
```

Another example of decidabile property is the equality for natural
numbers. In this case, when we compare two numbers of the form `succ
x` and `succ y`, we first decide whether `x` and `y` are equal. If
they are not, then we conclude that `succ x` and `succ y` must be
different (recall that constructors such as `succ` are
injective). If `x` and `y` are equal, then they can be unified and
we can prove `succ x == succ y` by reflexivity.

```
Nat-eq-decidable : ∀(x y : ℕ) -> Decidable (x == y)
Nat-eq-decidable zero     zero     = yes refl
Nat-eq-decidable zero     (succ y) = no λ ()
Nat-eq-decidable (succ x) zero     = no λ ()
Nat-eq-decidable (succ x) (succ y) with Nat-eq-decidable x y
... | no  neq  = no λ { refl -> neq refl }
... | yes refl = yes refl
```

As a final example we show that the equality of lists is decidable,
provided that the equality between their elements is also decidable.

```
List-eq-decidable : ∀{A : Set} -> (∀(x y : A) -> Decidable (x == y)) -> (xs ys : List A) -> Decidable (xs == ys)
List-eq-decidable _==?_ []        []        = yes refl
List-eq-decidable _==?_ []        (x :: ys) = no λ ()
List-eq-decidable _==?_ (x :: xs) []        = no λ ()
List-eq-decidable _==?_ (x :: xs) (y :: ys) with x ==? y | List-eq-decidable _==?_ xs ys
... | no  neq  | _        = no λ { refl -> neq refl }
... | yes _    | no  neq  = no λ { refl -> neq refl }
... | yes refl | yes refl = yes refl
```

The case in which we compare two lists of the form `x :: xs` and `y
:: ys` illustrates the use of multiple `with` clauses. In this case,
we have to compare both the heads and the tails of the two
lists. Only if both components are equal can we conclude that the
original lists are equal. Note that each case after the `with`
clauses has as many patterns as the number of `with` clauses.

-->

## Exercises

1. Prove the theorem `ntop : ¬ ⊤ -> ⊥`.
2. Which of the following De Morgan's laws can be proved?
   ```text
   ¬ A ∨ ¬ B -> ¬ (A ∧ B)
   ¬ A ∧ ¬ B -> ¬ (A ∨ B)
   ¬ (A ∨ B) -> ¬ A ∧ ¬ B
   ¬ (A ∧ B) -> ¬ A ∨ ¬ B
   ```
3. Show that the excluded middle implies double negation
   elimination, namely prove the theorem `em-dn : (∀{A : Set} -> ¬ A
   ∨ A) -> ∀{A : Set} -> ¬ ¬ A -> A`
4. Prove the theorem `nndec : ∀{A : Set} -> ¬ ¬ Decidable A`. Hint:
   one of the De Morgan's laws helps.
5. In classical logic the double negation elimination `¬ ¬ A -> A`
   is usually assumed to be true. This is not the case in
   constructive logic. Show that double negation elimination implies
   the excluded middle, namely prove the theorem `dn-em : (∀{A : Set}
   -> (¬ ¬ A -> A)) -> ∀{A : Set} -> Decidable A `. Hint: use the
   solution to the previous exercise.
```
-- EXERCISE 1

ntop : ¬ ⊤ -> ⊥
ntop p = p <>

-- EXERCISE 2: all laws but the last one can be proved.

de-morgan-1 : ∀{A B : Set} -> ¬ A ∨ ¬ B -> ¬ (A ∧ B)
de-morgan-1 = ∨-elim (contrapositive fst) (contrapositive snd)

de-morgan-2 : ∀{A B : Set} -> ¬ A ∧ ¬ B -> ¬ (A ∨ B)
de-morgan-2 p = ∨-elim (fst p) (snd p)

de-morgan-3 : ∀{A B : Set} -> ¬ (A ∨ B) -> ¬ A ∧ ¬ B
de-morgan-3 nab = contrapositive inl nab , contrapositive inr nab

-- EXERCISE 3

em-dn : (∀{A : Set} -> ¬ A ∨ A) -> ∀{A : Set} -> ¬ ¬ A -> A
em-dn f {A} g with f {A}
... | inl x = ex-falso (g x)
... | inr x = x

-- EXERCISE 4

nndec : ∀{A : Set} -> ¬ ¬ Decidable A
nndec p with de-morgan-3 p
... | nna , na = nna na

-- EXERCISE 5

dn-em : (∀{A : Set} -> (¬ ¬ A -> A)) -> ∀{B : Set} -> Decidable B
dn-em f = f nndec
```
{:.solution}
