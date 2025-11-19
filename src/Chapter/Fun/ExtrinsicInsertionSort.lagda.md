---
title: Extrinsic verification of insertion sort
prev:  Chapter.Fun.SortedLists
next:  Chapter.Fun.IntrinsicInsertionSort
---

```
module Chapter.Fun.ExtrinsicInsertionSort where
```

In this chapter we prove that *insertion sort*, one of the most
basic sorting algorithms, is correct, namely that it satisfies the
sorting specification defined in the [previous chapter]({% link
_pages/Chapter.Fun.SortedLists.md %}). We call *extrinsic
verification* this form of proof since we will define the algorithm
and the proof as separate entities. In contrast, in the [next
chapter]({% link _pages/Chapter.Fun.IntrinsicInsertionSort.md %}) we
will see an *intrinsic form* of verfication whereby the algorithm is
correct "by construction", in the sense that it incorporates the
proof that it satisfies the specification.

## Imports

```
open import Library.Logic
open import Library.Nat
open import Library.List
open import Library.LessThan
open import Chapter.Fun.SortedLists
```

## Insertion Sort

Insertion sort is based on a straightforward induction on the
structure of the list to be sorted. Each element of the list is
inserted in the right place in the sorted remainder of the list. For
this reason, most of the work is performed by an auxiliary function
`insert` that, given an element `x` and a (sorted) list `xs`,
creates a new list in which `x` has been inserted in the right
position of `xs` so that the result is still sorted.

```
insert : ℕ -> List ℕ -> List ℕ
insert x [] = [ x ]
insert x (y :: ys) with le-total x y
... | inl _ = x :: y :: ys
... | inr _ = y :: insert x ys
```

Note the use of `le-total` to check the relation between `x` and
`y`. If `x <= y` then `x` will be positioned first since, from the
hypothesis that the list `y :: ys` is sorted, we deduce that it is
the smallest element overall. If `y <= x` then `y` is the smallest
element and `x` must be inserted somewhere within `ys`. We can now
implement `insertion-sort` thus.

```
insertion-sort : List ℕ -> List ℕ
insertion-sort []        = []
insertion-sort (x :: xs) = insert x (insertion-sort xs)
```

To see that `insertion-sort` operates correctly, let us consider any
random list of natural numbers, such as `ls` below.

```agda
ls : List ℕ
ls = 23 :: 45 :: 7 :: 867 :: 76 :: 43 :: 32 :: 21 :: 123 :: 344 :: 5 :: []
```

By entering `C-c C-n insert-sort ls` we obtain the following list,
which is sorted.

    5 :: 7 :: 21 :: 23 :: 32 :: 43 :: 45 :: 76 :: 123 :: 344 :: 867 :: []

## Insertion sort generates a sorted list

We have seen that in the insertion sort algorithm most of the work
is performed by the auxiliary function `insert`. Not surprisingly,
this means that most of the verification efforts are made proving
key properties of `insert` with respect to the various predicates
that we have defined. We start from `LowerBound` and prove that if
`x <= y` and `x` is a lower bound for `ys`, then `x` is a lower
bound also for the list obtained by inserting `y` in `ys`.

```
lower-bound-insert : ∀{x y : ℕ} {ys : List ℕ} -> x <= y -> LowerBound x ys ->
                     LowerBound x (insert y ys)
lower-bound-insert x≤y lb-[] = lb-:: x≤y lb-[]
lower-bound-insert {x} {y} {z :: ys} x≤y (lb-:: x≤z x≤ys) with le-total y z
... | inl y≤z = lb-:: x≤y (lb-:: x≤z x≤ys)
... | inr z≤y = lb-:: x≤z (lower-bound-insert x≤y x≤ys)
```

Note that we have to perform a case analysis on `le-total y z` when
we deal with the case of non-empty lists to match the definition of
`insert`. To do that, we give names to the implicit arguments of the
function. We could have omitted `x` and `ys`, but in this way it is
clearer to see what the proofs `x≤y` and `x≤ys` refer to.

Using this result (as well as `lower-lower-bound` which was proposed
as an exercise in the [previous chapter]({% link
_pages/Chapter.Fun.SortedLists.md %})), we prove that `insert x ys`
is a sorted list if so is `ys`.

```
sorted-insert : ∀(x : ℕ) (ys : List ℕ) -> Sorted ys -> Sorted (insert x ys)
sorted-insert x [] sorted-[] = sorted-:: lb-[] sorted-[]
sorted-insert x (y :: ys) (sorted-:: y≤ys ys-sorted) with le-total x y
... | inl x≤y = sorted-:: (lb-:: x≤y (lower-lower-bound x≤y y≤ys))
                          (sorted-:: y≤ys ys-sorted)
... | inr y≤x = sorted-:: (lower-bound-insert y≤x y≤ys)
                          (sorted-insert x ys ys-sorted)
```

The proof that `insertion-sort xs` is sorted is now obtained by
induction on `xs`, using the previous lemmas.

```
sorted-insertion-sort : ∀(xs : List ℕ) -> Sorted (insertion-sort xs)
sorted-insertion-sort [] = sorted-[]
sorted-insertion-sort (x :: xs) =
  sorted-insert x (insertion-sort xs) (sorted-insertion-sort xs)
```

## Insertion sort generates a permutation

We now proceed by showing that the list `insertion-sort xs` is a
permutation of `xs`. As usual, we have to formulate a related
property also for the auxiliary function `insert`. In particular, we
need to show that the list `insert x ys` is a permutation of `x ::
ys`.

```
insert-permutation : ∀(x : ℕ) (ys : List ℕ) -> insert x ys # (x :: ys)
insert-permutation x [] = #refl
insert-permutation x (y :: ys) with le-total x y
... | inl x≤y = #refl
... | inr y≤x =
  #begin
    y :: insert x ys #⟨ #cong (insert-permutation x ys) ⟩
    y :: x :: ys     #⟨ #swap ⟩
    x :: y :: ys
  #end
```

In the two sub-cases that depend on the relationship between `x` and
`y` we have to consider the shape of the resulting list, which is `x
:: y :: ys` when `x <= y` and `y :: insert x ys` otherwise (see the
definition of `insert`). In the first sub-case no permutation is
necessary, so we just use reflexivity. In the second case we use the
induction hypothesis and then a single swap to move `x` to the front
of the list.

The proof that `insertion-sort xs` generates a permutation of `xs`
is now a simple matter.

```
insertion-sort-permutation : ∀(xs : List ℕ) -> insertion-sort xs # xs
insertion-sort-permutation [] = #refl
insertion-sort-permutation (x :: xs) =
  #begin
    insertion-sort (x :: xs)     #⟨ #refl ⟩
    insert x (insertion-sort xs) #⟨ insert-permutation x (insertion-sort xs) ⟩
    x :: insertion-sort xs       #⟨ #cong (insertion-sort-permutation xs) ⟩
    x :: xs
  #end
```

The application of reflexivity in the inductive case uses the fact
that `insertion-sort (x :: xs)` is definitionally equal to `insert x
(insertion-sort xs)`. This step is not strictly necessary, but it
helps to clarify the proof as it shows every non-trivial rewriting
that takes place.

## Putting it all together

We can now provide a verified version of insertion sort that
satisfies the `SortingFunction` specification.

```
verified-insertion-sort : SortingFunction
verified-insertion-sort xs =
  insertion-sort xs , insertion-sort-permutation xs , sorted-insertion-sort xs
```
