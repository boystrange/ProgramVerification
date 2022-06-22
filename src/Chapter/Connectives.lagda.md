---
title: Logical connectives
---

<!--
```
module Chapter.Connectives where

open import Fun
```
-->

The logic we have been using so far is based on a small set of
operators that correspond to a limited set of Agda types:

* The arrow type corresponds to **logical implication**: a proof of
  `A -> B` is a function that, applied to a proof of `A`, yields a
  proof of `B`.
* The dependent arrow type corresponds to **universal
  quantification**: a proof of `(x : A) -> B` is a function that,
  applied to an element `x` of type `A`, yields a proof of `B`
  (where `x` may occur in `B`).
* The **equality predicate** `E == F` is the type of proofs showing
  that `E` is equal to `F`.

In general, we will need a richer set of logical connectives in
order to prove interesting properties of programs. For example, to
prove the correctness of a sorting function on lists we must be able
to state that the list resulting from the function is sorted *and*
is a permutation of the original list. In this chapter we will
develop a small library of data types representing **conjunction**,
**disjunction**, **truth** and **falsity**.

## Conjunction

In constructive logic, a proof of a conjunction `A ∧ B` is a
**pair** `(p , q)` consisting of a proof `p` of `A` and a proof `q`
of `B`. Thus, we can define conjunction as a data type for
representing pairs. Naturally, the data type will be parametric in
the type of the two components of the pair.

```
data _∧_ (A B : Set) : Set where
  _,_ : A -> B -> A ∧ B
```

Notice that we have chosen an infix form for both the data type and
its only constructor: we will be able to write `A ∧ B` for the type
of pairs whose first component has type `A` and whose second
component has type `B`; we will be able to write `p , q` for the
pair whose first component is `p` and whose second component is
`q`. We specify the fixity of `∧` and `,` so that they are both
right associative.

```
infixr 3 _∧_
infixr 4 _,_
```

This way, `A ∧ B ∧ C` and `p , q , r` must be interpreted as `A ∧ (B
∧ C)` and `p , (q , r)`, respectively.

The most common way of "consuming" pairs is by performing case
analysis on them. Since the `_∧_` data type has only one
constructor, when we perform case analysis we end up considering
just one case in which the pair has the form `(x , y)`. As an
example, we can define two projections `fst` and `snd` that allow us
to access the two components of a pair.

```
fst : {A B : Set} -> A ∧ B -> A
fst (x , _) = x

snd : {A B : Set} -> A ∧ B -> B
snd (_ , y) = y
```

Note that `fst` and `snd` are also proofs of two well-known theorems
about conjunctions: if `A ∧ B` is true, then `A` is true (`fst`) and
`B` is true (`snd`).

By combining conjunction (given by the data type `∧`) and
implication (given by the native Agda's arrow type `->`) we can also
model double implication, commonly known as "if and only if".

```
_<=>_ : Set -> Set -> Set
A <=> B = (A -> B) ∧ (B -> A)
```

<!--
```
infixr 1 _<=>_
```
---

For example, we can prove the theorem `(A ∧ B) <=> (B ∧ A)` as
follows.

## Disjunction

In constructive logic, a proof of a disjunction `A ∨ B` is either a
proof of `A` or a proof of `B` together with an indication of which
proof it is. This interpretation suggests the representation of
disjunction `∨` as a data type with two constructors, one taking a
proof of `A` and the other taking a proof of `B`, to yield a proof
of `A ∨ B`. The name of the constructor indicates which of the two
proofs is provided. We call the two constructors `inl` and `inr` for
"inject left" and "inject right".

```
data _∨_ (A B : Set) : Set where
  inl : A -> A ∨ B
  inr : B -> A ∨ B
```

We declare `∨` as a right associative operator with smaller
precedence than `∧`.

```
infixr 2 _∨_
```

As for conjunctions, we will use case analysis on terms of type `A ∨
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

```
∨-elim : {A B C : Set} -> (A -> C) -> (B -> C) -> A ∨ B -> C
∨-elim f g (inl x) = f x
∨-elim f g (inr x) = g x
```

For instance, we can use `∨-elim` to prove that disjunction is
commutative:

```
∨-comm : {A B : Set} -> A ∨ B -> B ∨ A
∨-comm = ∨-elim inr inl
```

## Truth

The trivially true proposition `⊤` is represented as a data type
with a single constructor without arguments.

```
data ⊤ : Set where
  <> : ⊤
```

## Falsity and negation

The false proposition `⊥` must not be provable. As such, it is
represented by a data type without constructors.

```
data ⊥ : Set where
```

The elimination principle for `⊥` is sometimes called *principle of
explosion* or *ex falso quodlibet*. It states that if it is possible
to prove `⊥`, then it is possible to prove anything. Stating this
principle in Agda requires the use of the **absurd pattern**.

```
absurd : {A : Set} -> ⊥ -> A
absurd ()
```

The pattern `()` in the definition of `absurd` indicates a value of
type `⊥`. Since no constructor is provided for `⊥`, such impossible
value is denoted by `()` in an equation for `absurd` that *has no
right hand side* (note that there is no equal sign): as there is no
proof of `⊥`, we are not obliged to provide a proof of `A` as
required by the codomain of `absurd`.

In constructive logic, the `⊥` data type has a fundamental role
since it allows us to define negation. In particular, the negation
of a proposition `A` is a function that, given a proof of `A`,
provides a proof of `⊥`.

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

## Exercises

1. Prove that conjunction is commutative, namely the theorem
   `∧-comm : {A B : Set} -> A ∧ B -> B ∧ A`.
2. Prove that `∧` and `∨` are idempotent, namely the theorems
   `∧-idem : {A : Set} -> A ∧ A <=> A` and `∨-idem : {A : Set} -> A
   ∨ A <=> A`.
3. Prove that `∧` distributes over `∨` on the left, namely the
   theorem `∧∨-dist : {A B C : Set} -> A ∧ (B ∨ C) => (A ∧ B) ∨ (A ∧
   C)`.
4. Prove that `⊤` is the unit of conjuction, namely the theorems
   `∧-unit-l : {A : Set} -> ⊤ ∧ A <=> A` and `∧-unit-r : {A : Set}
   -> A ∧ ⊤ <=> A`.
5. Prove that `⊤` absorbs disjunctions, namely the theorems `∨-⊤-l :
   {A : Set} -> ⊤ ∨ A <=> ⊤` and `∨-⊤-r : {A : Set} -> A ∨ ⊤ <=> ⊤`.
6. Prove that `⊥` is the unit of disjunctions, namely the theorems
   `∨-unit-l : {A : Set} -> ⊥ ∨ A <=> A` and `∨-unit-r : {A : Set}
   -> A ∨ ⊥ <=> A`.
7. Prove that `⊥` absorbs conjunctions, namely the theorems `∧-⊥-l :
   {A : Set} -> ⊥ ∧ A <=> ⊥` and `∧-⊥-r : {A : Set} -> A ∧ ⊥ <=> ⊥`.
8. Prove the De Morgan law

```
-- EXERCISE 1
∧-comm : {A B : Set} -> A ∧ B -> B ∧ A
∧-comm (x , y) = y , x

-- EXERCISE 2
∧-idem : {A : Set} -> A ∧ A <=> A
∧-idem = fst , λ x -> (x , x)

∨-idem : {A : Set} -> A ∨ A <=> A
∨-idem = ∨-elim id id , inl

-- EXERCISE 3
∧∨-dist : {A B C : Set} -> A ∧ (B ∨ C) <=> (A ∧ B) ∨ (A ∧ C)
∧∨-dist =
  (λ p -> ∨-elim (inl ∘ (fst p ,_)) (inr ∘ (fst p ,_)) (snd p)) ,
  ∨-elim (λ p -> fst p , inl (snd p)) (λ p -> fst p , inr (snd p))

-- EXERCISE 4
∧-unit-l : {A : Set} -> ⊤ ∧ A <=> A
∧-unit-l = snd , (<> ,_)

∧-unit-r : {A : Set} -> A ∧ ⊤ <=> A
∧-unit-r = fst , (_, <>)

-- EXERCISE 5
∨-unit-l : {A : Set} -> ⊥ ∨ A <=> A
∨-unit-l = ∨-elim absurd id , inr

∨-unit-r : {A : Set} -> A ∨ ⊥ <=> A
∨-unit-r = ∨-elim id absurd , inl

-- EXERCISE 6
∨-⊤-l : {A : Set} -> ⊤ ∨ A <=> ⊤
∨-⊤-l = const <> , inl

∨-⊤-r : {A : Set} -> A ∨ ⊤ <=> ⊤
∨-⊤-r = const <> , inr

-- EXERCISE 7
∧-⊥-l : {A : Set} -> ⊥ ∧ A <=> ⊥
∧-⊥-l = fst , absurd

∧-⊥-r : {A : Set} -> A ∧ ⊥ <=> ⊥
∧-⊥-r = snd , absurd

-- EXERCISE 8
de-morgan-∧ : {A B : Set} -> ¬ (A ∧ B) -> ¬ A ∨ ¬ B
de-morgan-∧ p = {!!}

prop : {A B : Set} -> ¬ A ∨ ¬ B -> ¬ (A ∧ B)
prop = ∨-elim (contrapositive fst) (contrapositive snd)

de-morgan-∨ : {A B : Set} -> ¬ (A ∨ B) -> ¬ A ∧ ¬ B
de-morgan-∨ p = (p ∘ inl) , (p ∘ inr)
```

