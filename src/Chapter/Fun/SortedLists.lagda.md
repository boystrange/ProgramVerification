---
title: Specification of a sorting algorithm
---

In this chapter we address the problem of specifying the type of a
*sorting algorithm* on lists. This specification will be
instrumental in the following chapters, where we will verify the
correctness of some sorting algorithms.

<!--
```
open import Fun
open import Logic
open import Equality
open import List using (List; []; _::_; [_]; reverse; _++_)
open import List.Properties
```
-->

## Modules with parameters

Since we are going to implement and verify polymorphic sorting
algorithms, we assume to work with a given type `A` of the elements
of the lists being sorted and a total order relation `_≼_` over such
elements. We specify these assumptions as parameters to the modules
in which they are necessary. For instance, the module corresponding
to this chapter is declared thus.

```
module Chapter.Fun.SortedLists
  (A       : Set)
  (_≼_     : A -> A -> Set)
  (≼-refl  : {x : A} -> x ≼ x)
  (≼-trans : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z)
  (≼-total : (x y : A) -> x ≼ y ∨ y ≼ x)
  where
```

We have specified the properties `≼-refl`, `≼-trans` and `≼-total`
as an illustration of module parameters, but we are not going to use
any of these properties of `≼` in this chapter.

## What is a sorting function?

There are various levels at which we can specify the type of a
sorting function. The most basic - and less informative -
specification is that of a function from lists to lists:

* A sorting function takes a list of elements of type `A` and
  returns a list of elements of type `A`.

This specification is very imprecise, as it characterizes many
functions that have nothing to do with sorting. For example, both
the identity function and the constant function that always yields
`[]` satisfy this specification. We can refine this specification
stating that the resulting list should be sorted:

* A sorting function takes a list of elements of type `A` and
  returns a *sorted* list of elements of type `A`.

A function satisfying this property is guaranteed to return a sorted
list, but the specification is still weak. For example, the constant
function that always returns `[]` would satisfy this specification,
since `[]` is trivially sorted.

The final refinement of our specification takes into account the
fact that the resulting list should contain the same elements as the
original list, possibly in a different order. Technically, the
returned list should be a permutation of the original one:

* A sorting function takes a list `xs` of elements of type `A` and
  returns a *sorted* list `ys` of elements of type `A` that is a
  *permutation* of `xs`.

In this specification, we are somehow forced to give names to the
original and returned lists, since we want to relate them
closely. This suggests that we will make use of dependent and
existential types to formalize this specification in Agda.

We now proceed specifying first what it means for a list to be
sorted (according to `≼`) and then what it means for a list to be a
permutation of another list.

## Sorted lists

In order to define a "sorted" predicate for lists, it is useful to
define an auxiliary predicate `≼*` such that `x ≼* xs` holds if `x`
is a *lower bound* for all of the elements in the list `xs`. To this
aim, we define a parametric `All` predicate such that `All P xs`
holds if so does `P x` for each element `x` of `xs`.

```
All : {A : Set} -> (A -> Set) -> List A -> Set
All P []        = ⊤
All P (x :: xs) = P x ∧ All P xs
```

Note that `All P xs` is an example of type-level computation and is
defined by structural induction on `xs` by creating a conjunction of
propositions concerning each individual element `x` of `xs`. In
general, we have

    All P (x₁ :: x₂ :: ... :: xₙ :: []) = P x₁ ∧ P x₂ ∧ ... ∧ P xₙ

We can obtain `≼*` as a simple specialization of `All`, thus:

```
_≼*_ : A -> List A -> Set
x ≼* xs = All (x ≼_) xs
```

Note that we are creating the predicate "being ≼-larger than `x`" by
means of the expression `(x ≼_)`, in which we supply the left
operand of `≼` (that is `x`) but not the right operand of `≼`. This
expression is just a short form for the abstraction `λ y -> x ≼ y`.

We make use of type-level computation once more to define the
`Sorted` predicate: the empty list is trivially sorted. A non-empty
list with head `x` and tail `xs` is sorted if `x` is a lower bound
of `xs` and if `xs` is in turn sorted.

```
Sorted : List A -> Set
Sorted []        = ⊤
Sorted (x :: xs) = x ≼* xs ∧ Sorted xs
```

It is easy to prove that every singleton list is sorted.

```
singleton-sorted : (x : A) -> Sorted [ x ]
singleton-sorted _ = <> , <>
```

## Permutations

Next we have to define a binary predicate `_#_` over lists such that
`xs # ys` holds whenever `xs` is a permutation of `ys`. We establish
that `ys` is a permutation of `xs` if `ys` is obtained by a finite
sequence of *swaps* starting from `xs`, whereby each swap exchanges
the position of two subsequent elements in a list. In the simplest
case, the swapped elements are found just at the beginning of the
list, so we start by defining the following axiom.

    [#swap] ---------------------------
            x :: y :: xs # y :: x :: xs

In general, we might want to swap two subsequent elements of a list
no matter how deep they are found within the list. So we extend the
predicate with the following congruence rule.

                 xs # ys
    [#cong] -----------------
            x :: xs # x :: ys

Finally, we take the reflexive and transitive closure of the swap
relation defined so far, which allows us to combine an arbitrary
number of swaps into a permutation.

                                xs # ys     ys # zs
    [#refl] -------    [#trans] -------------------
            xs # xs                   xs # zs

Similarly to what we have done for the "less than" relation, we
define this inference system as an Agda data type. The data type has
one parameter `A`, the type of the elements of the lists, and two
indices which are the lists being related.

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
Library]({% link pages/List.Permutation.html %}).

## Putting it all together

A sorting function is a function that takes a list `xs` and yields a
triple consisting of another list `ys`, a proof that `ys` is a
permutation of `xs`, and a proof that `ys` is sorted.

```
SortingFunction : Set
SortingFunction = (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
```

## Exercises

The following is an alternative definition of sorted list based on
the intuition that the empty list and every singleton list are
trivially sorted and that a list with two or more elements is sorted
if the first element is `≼`-smaller than the second one, and if the
sub-list starting from the second element is sorted.

```
Sorted' : List A -> Set
Sorted' []             = ⊤
Sorted' (_ :: [])      = ⊤
Sorted' (x :: y :: xs) = x ≼ y ∧ Sorted' (y :: xs)
```

Prove the following theorems asserting that `Sorted` and `Sorted'`
are equivalent.  What could make `Sorted'` less convenient to use
compared to `Sorted`?

```
Sorted->Sorted' : {xs : List A} -> Sorted xs -> Sorted' xs
Sorted'->Sorted : {xs : List A} -> Sorted' xs -> Sorted xs
```

```
Sorted->Sorted' {[]}           p               = <>
Sorted->Sorted' {x :: []}      p               = <>
Sorted->Sorted' {x :: y :: xs} ((x≼y , _) , q) = x≼y , Sorted->Sorted' q

Sorted'->Sorted {[]}      p = <>
Sorted'->Sorted {x :: []} p = <> , <>
Sorted'->Sorted {x :: y :: xs} (x≼y , p) = (x≼y , lem x≼y p) , Sorted'->Sorted p
  where
    lem : {x y : A} {xs : List A} -> x ≼ y -> Sorted' (y :: xs) -> All (x ≼_) xs
    lem {_} {_} {[]} x≼y p = <>
    lem {x} {y} {z :: xs} x≼y (y≼z , p) = ≼-trans x≼y y≼z , lem (≼-trans x≼y y≼z) p
```
{:.solution}

Prove the following theorem, asserting that list predicates defined
using `All` are preserved by permutations.

```
#All : {A : Set} (P : A -> Set) {xs ys : List A} -> xs # ys -> All P xs -> All P ys
```

```
#All P #refl         ps           = ps
#All P #swap         (p , q , ps) = q , p , ps
#All P (#cong π)     (p , ps)     = p , #All P π ps
#All P (#trans π π') ps           = #All P π' (#All P π ps)
```

Prove the following theorem asserting that the first element of any
list can be pushed arbitrarily deep into list still obtaining a
permutation of the original list.

```
#push : {A : Set} (x : A) (xs ys : List A) -> x :: xs ++ ys # xs ++ x :: ys
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
#++ : {A : Set} (xs ys : List A) -> xs ++ ys # ys ++ xs
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
#reverse : {A : Set} (xs : List A) -> reverse xs # xs
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
