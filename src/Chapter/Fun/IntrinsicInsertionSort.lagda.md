---
title: Intrinsic verification of insertion sort
prev:  Chapter.Fun.ExtrinsicInsertionSort
---

```
module Chapter.Fun.IntrinsicInsertionSort where
```

The extrinsic verification of insertion sort allowed us to prove the
correctness of insertion sort by considering each aspect of the
algorithm in isolation. Indeed, we have defined the algorithm
(`insertion-sort`), the proof that the algorithm yields a sorted
list (`sorted-insertion-sort`) and the proof that the algorithm
yields a permutation of the original list
(`insertion-sort-permutation`) as separate elements. It is easy to
observe that these elements are structurally related. In particular,
most proofs must perform a case analysis on an application of
`le-total` because that is the way in which the `insert` function is
defined. As a consequence, there is a certain amount of redundancy
in the proofs.

In this chapter we revisit the verification of insertion sort, but
we do so using a different approach called *intrinsic
verification*. In this approach, the implementation of the algorithm
and the proof of its properties are done simultaneously. As we will
see, the overall amount of Agda code we have to write is noticeably
smaller, although the code itself is necessarily more convoluted.

## Imports

```
open import Library.Logic
open import Library.Nat
open import Library.List
open import Library.LessThan
open import Chapter.Fun.SortedLists
```

## Intrinsically verified insertion

As expected, if we aim at providing an intrinsically verified
insertion sort we have to provide an intrinsically verified
insertion operation, which we specify thus.

```
intrinsic-insert : ∀(x : ℕ) (ys : List ℕ) -> Sorted ys ->
                   ∃[ zs ] zs # x :: ys ∧ Sorted zs
```

In words, the insert operation applied to a number `x` and a sorted
list `ys` yields another sorted list `zs` that is a permutation of
`x :: ys`. Note that now the function takes not only the element and
the list on which it operates, but also a proof that the list is
sorted.

The base case in which `ys` is empty is handled by the following
equation.

```
intrinsic-insert x [] sorted-[] = [ x ] , #refl , sorted-:: lb-[] sorted-[]
```

Remeber that a proof of an existential quantification `∃[ x ] P` is
a pair consisting of a witness and a proof that the witness
satisfies `P`. In this case, the predicate `P` is a conjunction
whose proof is itself a pair. For this reason, `intrinsic-insert`
yields a *triple* made of the witness, which is the singleton list
`[ x ]`, a proof that `[ x ]` is a permutation of `x :: []` and a
proof that `[ x ]` is sorted. Recall from the definition of `[_]`
that `[ x ]` and `x :: []` are definitionally equal, so `#refl`
suffices to prove that they are one the permutation of the other.

When we are inserting `x` in a non-empty list `y :: ys` we have to
establish the relationship between `x` and `y`, which we do by
performing case analysis on `le-total x y`.

```
intrinsic-insert x (y :: ys) (sorted-:: y≤ys ys-sorted) with le-total x y
```

Since the list in which we are inserting `x` is not empty, the proof
that it is sorted must have the form `sorted-:: y≤ys ys-sorted`,
which contains a sub-proof that `y` is a lower bound for `ys` and
that `ys` is itself sorted. Let us now consider the case in which `x
<= y`.

```
... | inl x≤y = x :: y :: ys ,
                #refl ,
                sorted-:: (lb-:: x≤y (lower-lower-bound x≤y y≤ys))
                          (sorted-:: y≤ys ys-sorted)
```

Here `x` is inserted just at the front of the list, so no swapping
is necessary and `#refl` suffices as far as permutations are
concerned. In order to prove that the resulting list is sorted we
need a proof that `x` is a lower bound for `y :: ys`, which we
obtain from the proof that `y` is a lower bound for `ys` along with
the hypothesis `x≤y` using the `lower-lower-bound` lemma that we
have proved in a previous chapter.

```
... | inr y≤x with intrinsic-insert x ys ys-sorted
```

If `y <= x`, then we have to insert `x` in `ys`. This operation will
not only return the resulting list `zs`, but also a proof `π` that
`zs` is a permutation of `x :: ys` and a proof `zs-sorted` that `zs`
is sorted. We combine these proofs in the result of the function.

```
... | zs , π , zs-sorted =
  y :: zs ,
  (#begin
    y :: zs      #⟨ #cong π ⟩
    y :: x :: ys #⟨ #swap ⟩
    x :: y :: ys
  #end) ,
  sorted-:: (lower-bound-permutation π (lb-:: y≤x y≤ys)) zs-sorted
```

## Intrinsically verified insertion sort

We are now ready to complete the intrinsic verification of insertion
sort.

```
verified-insertion-sort : SortingFunction
```

In the base case, when the list to be sorted is empty, there isn't
much to do except providing the easy proofs that the empty list is
sorted and a permutation of itself.

```
verified-insertion-sort [] = [] , #refl , sorted-[]
```

In the inductive case, first of all we recursively sort the tail of
the list.

```
verified-insertion-sort (x :: xs) with verified-insertion-sort xs
```

By performing case analysis we get access to the resulting list
`ys`, a proof `ys#xs` that `ys` is a permutation of `xs` and a proof
`ys-sorted` that `ys` is sorted. Now we can insert `x` into `ys`.

```
... | ys , ys#xs , ys-sorted with intrinsic-insert x ys ys-sorted
```

We do case analysis on the result once again so that we get access
to the resulting list `zs`, the proof `π` that `zs` is a permutation
of `x :: ys` and the proof `zs-sorted` that `zs` is sorted. The
proof that `zs` is a permutation of `x :: xs` follows from
transitivity of permutations and the sub-proofs `ys#xs` and `π`.

```
... | zs , π , zs-sorted =
  zs ,
  (#begin
    zs      #⟨ π ⟩
    x :: ys #⟨ #cong ys#xs ⟩
    x :: xs
  #end) ,
  zs-sorted
```
