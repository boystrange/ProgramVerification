---
title: Negation
prev:  Chapter.Logic.Connectives
next:  Chapter.Logic.Existential
---

```
open import Library.Bool
open import Library.Nat
open import Library.List
open import Library.Fun
open import Library.Equality
open import Chapter.Logic.Connectives

module Chapter.Logic.Negation where
```

## Constructive negation

In constructive logic, the `⊥` data type has a fundamental role
since it allows us to define negation. To show that the *negation*
of a proposition `A` holds amounts to show that a proof of `A` can
be turned into a proof of `⊥`.

```
¬_ : Set -> Set
¬_ A = A -> ⊥
```

We will make a rather extensive use of negation in the following
chapters. For the time being, we prove two laws related to
negation. The first one is the **law of contraposition**, asserting
that if `A` implies `B`, then `¬ B` implies `¬ A`.

```
contrapositive : {A B : Set} -> (A -> B) -> ¬ B -> ¬ A
contrapositive f p q = p (f q)
```

The second law is **double negation**, asserting that if `A` is
true, then it is not true that the negation of `A` is true.

```
double-negation : {A : Set} -> A -> ¬ ¬ A
double-negation x p = p x
```

## Decidability

In classical logic it is common to assume the validity of the
*excluded middle* principle, namely that `¬ A ∨ A` is true for every
proposition `A`. As we know from the [previous chapter]({% link
pages/Chapter.Logic.Connectives.md %}), in constructive logic, a proof of
a disjunction `¬ A ∨ A` embeds either a proof of `¬ A` or a proof of
`A`, hence it may very well be the case that we are unable to prove
`¬ A ∨ A` if we cannot find either a proof of `¬ A` or a proof of
`A`. The propositions for which we are able to prove `¬ A ∨ A` are
said to be **decidable**.

```
Decidable : Set -> Set
Decidable A = ¬ A ∨ A
```

The equality between boolean values is decidable. This can be shown
by considering all the possible cases, which are finite.

```
Bool-eq-decidable : (x y : Bool) -> Decidable (x == y)
Bool-eq-decidable true  true  = inr refl
Bool-eq-decidable true  false = inl λ ()
Bool-eq-decidable false true  = inl λ ()
Bool-eq-decidable false false = inr refl
```

The equality for natural numbers is also decidable. In this case,
when we compare two numbers of the form `succ x` and `succ y`, we
first decide whether `x` and `y` are equal. If they are not, then we
conclude that `succ x` and `succ y` must be different (recall that
constructors such as `succ` are injective). If `x` and `y` are
equal, then they can be unified and we can prove `succ x == succ y`
by reflexivity.

```
Nat-eq-decidable : (x y : ℕ) -> Decidable (x == y)
Nat-eq-decidable zero     zero     = inr refl
Nat-eq-decidable zero     (succ y) = inl λ ()
Nat-eq-decidable (succ x) zero     = inl λ ()
Nat-eq-decidable (succ x) (succ y) with Nat-eq-decidable x y
... | inl neq  = inl λ { refl -> neq refl }
... | inr refl = inr refl
```

As a final example we show that the equality of lists is decidable,
provided that so is the equality between their elements.

```
List-eq-decidable : {A : Set} -> ((x y : A) -> Decidable (x == y)) -> (xs ys : List A) -> Decidable (xs == ys)
List-eq-decidable _==?_ []        []        = inr refl
List-eq-decidable _==?_ []        (x :: ys) = inl λ ()
List-eq-decidable _==?_ (x :: xs) []        = inl λ ()
List-eq-decidable _==?_ (x :: xs) (y :: ys) with x ==? y | List-eq-decidable _==?_ xs ys
... | inl neq  | _        = inl λ { refl -> neq refl }
... | inr _    | inl neq  = inl λ { refl -> neq refl }
... | inr refl | inr refl = inr refl
```

The case in which we compare two lists of the form `x :: xs` and `y
:: ys` illustrates the use of multiple `with` clauses. In this case,
we have to compare both the heads and the tails of the two
lists. Only if both components are equal can we conclude that the
original lists are equal. Note that each case after the `with`
clauses has as many patterns as the number of `with` clauses.

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
   elimination, namely prove the theorem `em-dn : ({A : Set} -> ¬ A
   ∨ A) -> {A : Set} -> ¬ ¬ A -> A`
4. Prove the theorem `nndec : {A : Set} -> ¬ ¬ Decidable A`. Hint:
   one of the De Morgan's laws helps.
5. In classical logic the double negation elimination `¬ ¬ A -> A`
   is usually assumed to be true. This is not the case in
   constructive logic. Show that double negation elimination implies
   the excluded middle, namely prove the theorem `dn-em : ({A : Set}
   -> (¬ ¬ A -> A)) -> {A : Set} -> Decidable A `. Hint: use the
   solution to the previous exercise.

```
-- EXERCISE 1

ntop : ¬ ⊤ -> ⊥
ntop p = p <>

-- EXERCISE 2: all laws but the last one can be proved.

de-morgan-1 : {A B : Set} -> ¬ A ∨ ¬ B -> ¬ (A ∧ B)
de-morgan-1 = ∨-elim (contrapositive fst) (contrapositive snd)

de-morgan-2 : {A B : Set} -> ¬ A ∧ ¬ B -> ¬ (A ∨ B)
de-morgan-2 p = ∨-elim (fst p) (snd p)

de-morgan-3 : {A B : Set} -> ¬ (A ∨ B) -> ¬ A ∧ ¬ B
de-morgan-3 nab = contrapositive inl nab , contrapositive inr nab

-- EXERCISE 3

em-dn : ({A : Set} -> ¬ A ∨ A) -> {A : Set} -> ¬ ¬ A -> A
em-dn f {A} g with f {A}
... | inl x = absurd (g x)
... | inr x = x

-- EXERCISE 4

nndec : {A : Set} -> ¬ ¬ Decidable A
nndec p with de-morgan-3 p
... | nna , na = nna na

-- EXERCISE 5

dn-em : ({A : Set} -> (¬ ¬ A -> A)) -> {B : Set} -> Decidable B
dn-em f = f nndec
```
