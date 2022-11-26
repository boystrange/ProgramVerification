---
title: Specification of a sorting algorithm
next:  Chapter.Fun.ExtrinsicInsertionSort
---

```
module Chapter.Fun.SortedLists where
```

In this chapter we address the problem of specifying the type of a
*sorting algorithm* on lists. This specification will be
instrumental in the following chapters, where we will verify the
correctness of some sorting algorithms. For the sake of simplicity
we will specify and verify sorting algorithms that work on lists of
natural numbers, but the Agda code can be easily generalized to work
with lists of arbitrary elements, provided that such elements are
equipped with a total order.

## Imports

```
open import Library.Fun
open import Library.Nat
open import Library.LessThan
open import Library.Logic
open import Library.Equality
open import Library.List using (List; []; _::_; [_]; reverse; _++_)
open import Library.List.Properties
```

## What is a sorting function?

There are various levels at which we can specify the type of a
sorting function. The most basic - and less informative -
specification is that of a function from lists to lists:

* A sorting function takes a list of elements of type `ℕ` and
  returns a list of elements of type `ℕ`.

This specification is very imprecise, as it characterizes many
functions that have nothing to do with sorting. For example, both
the identity function and the constant function that always yields
`[]` satisfy this specification. We can refine this specification
stating that the resulting list should be sorted:

* A sorting function takes a list of elements of type `ℕ` and
  returns a *sorted* list of elements of type `ℕ`.

A function satisfying this property is guaranteed to return a sorted
list, but the specification is still weak. For example, the constant
function that always returns `[]` would satisfy this specification,
since `[]` is trivially sorted.

The final refinement of our specification takes into account the
fact that the resulting list should contain the same elements as the
original list, possibly in a different order. Technically, the
returned list should be a permutation of the original one:

* A sorting function takes a list `xs` of elements of type `ℕ` and
  returns a *sorted* list `ys` of elements of type `ℕ` that is a
  *permutation* of `xs`.

In this specification, we are somehow forced to give names to the
original and returned lists, since we want to relate them
closely. This suggests that we will make use of dependent and
existential types to formalize this specification in Agda.

We now proceed specifying first what it means for a list to be
sorted and then what it means for a list to be a permutation of
another list.

## Sorted lists

In order to define a "sorted" predicate for lists, it is useful to
define an auxiliary predicate `LowerBound` such that `LowerBound x
xs` holds if `x` is a *lower bound* for all of the elements in the
list `xs`. We can define this predicate inductively by means of the
inference system below.

                                   x <= y    LowerBound x ys
    lb-[] ---------------    lb-:: -------------------------
          LowerBound x []           LowerBound x (y :: ys)

The element `x` is always a lower bound for the empty list, no
matter what `x` is. In order for `x` to be the lower bound of a
non-empty list `y :: ys`, it must be the case that `x <= y` and that
`x` is a lower bound for `ys` as well. The translation of this
inference system into an Agda data type is straightforward.

```
data LowerBound (x : ℕ) : List ℕ -> Set where
  lb-[] : LowerBound x []
  lb-:: : ∀{y : ℕ} {ys : List ℕ} -> x <= y -> LowerBound x ys ->
          LowerBound x (y :: ys)
```

A property of `LowerBound` that will be useful in the following is
the fact that a lower bound can be further lowered.

```
lower-lower-bound : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> LowerBound y ys ->
                    LowerBound x ys
lower-lower-bound x≤y lb-[] = lb-[]
lower-lower-bound x≤y (lb-:: y≤z y≤ys) =
  lb-:: (le-trans x≤y y≤z) (lower-lower-bound x≤y y≤ys)
```

We make use of `LowerBound` to define the `Sorted` predicate as
follows.

                                     LowerBound x xs    Sorted xs
    sorted-[] ---------    sorted-:: ----------------------------
              Sorted []                    Sorted (x :: xs)

The empty list is trivially sorted. A non-empty list `x :: xs` is
sorted provided that `x` is a lower bound for `xs` and `xs` is
sorted as well. In Agda code we obtain:

```
data Sorted : List ℕ -> Set where
  sorted-[] : Sorted []
  sorted-:: : ∀{x : ℕ} {xs : List ℕ} -> LowerBound x xs -> Sorted xs ->
              Sorted (x :: xs)
```

It is easy to prove that every singleton list is sorted.

```
singleton-sorted : ∀(x : ℕ) -> Sorted [ x ]
singleton-sorted _ = sorted-:: lb-[] sorted-[]
```

## Permutations

Next we have to define a binary predicate `_#_` over lists such that
`xs # ys` holds whenever `xs` is a permutation of `ys`. We establish
that `ys` is a permutation of `xs` if `ys` is obtained by a finite
sequence of *swaps* starting from `xs`, whereby each swap exchanges
the position of two subsequent elements in a list. In the simplest
case, the swapped elements are found just at the beginning of the
list, so we start by defining the following axiom.

    #swap ---------------------------
          x :: y :: xs # y :: x :: xs

In general, we might want to swap two subsequent elements of a list
no matter how deep they are found within the list. So we extend the
predicate with the following congruence rule.

               xs # ys
    #cong -----------------
          x :: xs # x :: ys

Finally, we take the reflexive and transitive closure of the swap
relation defined so far, which allows us to combine an arbitrary
number of swaps into a permutation.

                            xs # ys     ys # zs
    #refl -------    #trans -------------------
          xs # xs                 xs # zs

Similarly to what we have done for the "less than" relation, we
define this inference system as an Agda data type. Since the notion
of permutation of a list is unrelated to the type of its elements,
we can define a data type with one parameter `A`, the type of the
elements of the lists, and two indices which are the lists being
related.

```
infix  4 _#_

data _#_ {A : Set} : List A -> List A -> Set where
  #refl  : {xs : List A} -> xs # xs
  #swap  : {x y : A} {xs : List A} -> x :: y :: xs # y :: x :: xs
  #cong  : {x : A} {xs ys : List A} -> xs # ys -> x :: xs # x :: ys
  #trans : {xs ys zs : List A} -> xs # ys -> ys # zs -> xs # zs
```

As an example, the following term proves that $[1,2,3]$ is a
permutation of $[3,2,1]$.

```
_ : 1 :: 2 :: 3 :: [] # 3 :: 2 :: 1 :: []
_ = #trans (#trans #swap (#cong #swap)) #swap
```

The relation `#` is reflexive and transitive by definition, since
there are constructors corresponding to these properties. We can
prove that it is also *symmetric*, thus establishing that `#` is an
equivalence relation.

```
#symm : {A : Set} {xs ys : List A} -> xs # ys -> ys # xs
#symm #refl         = #refl
#symm #swap         = #swap
#symm (#cong π)     = #cong (#symm π)
#symm (#trans π π') = #trans (#symm π') (#symm π)
```

<!--
```
infix  1 #begin_
infixr 2 _#⟨⟩_ _#⟨_⟩_
infix  3 _#end

#begin_ : {A : Set} {xs ys : List A} -> xs # ys -> xs # ys
#begin_ ps = ps

_#end : {A : Set} (xs : List A) -> xs # xs
_#end xs = #refl

_#⟨_⟩_ : {A : Set} (xs : List A) {ys zs : List A} -> xs # ys -> ys # zs -> xs # zs
_#⟨_⟩_ _ = #trans

_#⟨⟩_ : {A : Set} (xs : List A) {ys : List A} -> xs # ys -> xs # ys
_ #⟨⟩ ps = ps
```
-->

In the following we will have to write some rather complex proofs
involving permutations. To simplify these proofs and make them more
readable, it is convenient to use some derived operators that allow
us to write chains of simpler permutation steps, in the same vein as
the reasoning blocks that allow us to write chains of equalities. In
general these chains have the form

    #begin E₁ #⟨ p₁ ⟩ E₂ #⟨ p₂ ⟩ E₃ ... Eₙ #end

where `E₁`, ..., `Eₙ` are lists, and each `pᵢ` proves (i.e., has
type) `Eᵢ # Eᵢ₊₁`. For example, we can provide the following
alternative proof of the fact that $[1,2,3]$ is a permutation of
$[3,2,1]$.

```
_ : 1 :: 2 :: 3 :: [] # 3 :: 2 :: 1 :: []
_ = #begin
      1 :: 2 :: 3 :: [] #⟨ #swap ⟩
      2 :: 1 :: 3 :: [] #⟨ #cong #swap ⟩
      2 :: 3 :: 1 :: [] #⟨ #swap ⟩
      3 :: 2 :: 1 :: []
    #end
```

We do not discuss the definition of these operators here, the
interested reader may found in the source code of the [Mini Agda
Library](List.Permutation.html).

## Putting it all together

A sorting function is a function that takes a list `xs` and yields a
triple consisting of another list `ys`, a proof that `ys` is a
permutation of `xs`, and a proof that `ys` is sorted.

```
SortingFunction : Set
SortingFunction = ∀(xs : List ℕ) -> ∃[ ys ] ys # xs ∧ Sorted ys
```

## Exercises

Prove that permutations preserve lower bounds.

```
lower-bound-permutation : ∀{x : ℕ} {xs ys : List ℕ} -> ys # xs ->
                          LowerBound x xs -> LowerBound x ys
```

```
lower-bound-permutation #refl x≤xs = x≤xs
lower-bound-permutation #swap (lb-:: x≤y (lb-:: x≤z x≤xs)) =
  lb-:: x≤z (lb-:: x≤y x≤xs)
lower-bound-permutation (#cong π) (lb-:: x≤y x≤xs) =
  lb-:: x≤y (lower-bound-permutation π x≤xs)
lower-bound-permutation (#trans π π') x≤xs =
  lower-bound-permutation π (lower-bound-permutation π' x≤xs)
```
{:.solution}

The following is an alternative definition of sorted list based on a
weaker notion of "lower bound" which only considers the head of a
list.

```
data HeadLowerBound : ℕ -> List ℕ -> Set where
  hlb-[] : ∀{x : ℕ} -> HeadLowerBound x []
  hlb-:: : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> HeadLowerBound x (y :: ys)

data Sorted' : List ℕ -> Set where
  sorted-[] : Sorted' []
  sorted-:: : ∀{x : ℕ} {xs : List ℕ} -> HeadLowerBound x xs -> Sorted' xs -> Sorted' (x :: xs)
```

Prove the following theorems asserting that `Sorted` and `Sorted'`
are equivalent.

```
Sorted->Sorted' : ∀{xs : List ℕ} -> Sorted xs -> Sorted' xs
Sorted'->Sorted : ∀{xs : List ℕ} -> Sorted' xs -> Sorted xs
```

```
Sorted->Sorted' sorted-[] = sorted-[]
Sorted->Sorted' (sorted-:: x≤xs p) = sorted-:: (lemma x≤xs) (Sorted->Sorted' p)
  where
    lemma : ∀{x : ℕ} {xs : List ℕ} -> LowerBound x xs -> HeadLowerBound x xs
    lemma lb-[] = hlb-[]
    lemma (lb-:: x≤y p) = hlb-:: x≤y

Sorted'->Sorted sorted-[] = sorted-[]
Sorted'->Sorted (sorted-:: p q) = sorted-:: (lemma p q) (Sorted'->Sorted q)
  where
    lower : ∀{x y : ℕ} {xs : List ℕ} -> x <= y -> HeadLowerBound y xs ->
            HeadLowerBound x xs
    lower x≤y hlb-[] = hlb-[]
    lower x≤y (hlb-:: y≤z) = hlb-:: (le-trans x≤y y≤z)

    lemma : ∀{x : ℕ} {xs : List ℕ} -> HeadLowerBound x xs -> Sorted' xs ->
            LowerBound x xs
    lemma hlb-[] sorted-[] = lb-[]
    lemma (hlb-:: x≤y) (sorted-:: p q) = lb-:: x≤y (lemma (lower x≤y p) q)
```
{:.solution}

Prove the following theorem asserting that the first element of any
list can be pushed arbitrarily deep into the list still obtaining a
permutation of the original list.

```
#push : ∀{A : Set} (x : A) (xs ys : List A) -> x :: xs ++ ys # xs ++ x :: ys
```

```
#push _ []        _ = #refl
#push x (y :: xs) ys =
  #begin
    x :: y :: xs ++ ys #⟨ #swap ⟩
    y :: x :: xs ++ ys #⟨ #cong (#push x xs ys) ⟩
    y :: xs ++ x :: ys
  #end
```
{:.solution}

Prove the following theorem showing that `xs ++ ys` and `ys ++ xs`
are one the permutation of the other.

```
#++ : ∀{A : Set} (xs ys : List A) -> xs ++ ys # ys ++ xs
```

```
#++ []        ys rewrite ++-unit-r ys = #refl
#++ (x :: xs) ys =
  #begin
    (x :: xs) ++ ys #⟨ #refl ⟩
    x :: xs ++ ys   #⟨ #cong (#++ xs ys) ⟩
    x :: ys ++ xs   #⟨ #push x ys xs ⟩
    ys ++ x :: xs
  #end
```
{:.solution}

Prove the following theorem, asserting that the reverse of `xs` is a
particular permutation of `xs`.

```
#reverse : ∀{A : Set} (xs : List A) -> reverse xs # xs
```

```
#reverse [] = #refl
#reverse (x :: xs) =
  #begin
    reverse (x :: xs)   #⟨ #refl ⟩
    reverse xs ++ [ x ] #⟨ #++ (reverse xs) [ x ] ⟩
    [ x ] ++ reverse xs #⟨ #refl ⟩
    x :: reverse xs     #⟨ #cong (#reverse xs) ⟩
    x :: xs
  #end
```
{:.solution}
