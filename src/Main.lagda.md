---
title: Main
---

This module imports **everything**, so that Agda can generate the
markdown files for all of the sources.

## Chapters

```agda
import Chapter.Demo
import Chapter.Setup
import Chapter.Lambda
import Chapter.Interactive

-- Booleans, first theorems using equality

-- Empty, Unit, Product, Sum

-- Logic, Curry-Howard isomorphism

-- Dependent arrow type, dependent product

-- Natural numbers, properties using equalities

-- Inductive families (being even, being equal)

-- Lists, properties

-- insertion sort (intrinsic and extrinsic)
import Chapter.InsertionSort

-- non-structural recursion using measures, intrinsic verification
import Chapter.QuickSort

-- Red black trees (embedding invariants in the definition of data structure,
-- mutual induction and mutual recursion, <= reasoning)
import Chapter.RedBlackTree

-- Regular expression matching (inference systems)
import Chapter.Regex

-- Euclidean division (termination, well founded recursion)
import Chapter.Division
```

## Library

```agda
import Bool
import Empty
import Equality
import Equality.Reasoning
import Fin
import Fun
import LessThan
import LessThan.Alternative
import LessThan.Reasoning
import List
import List.Permutation
import List.Properties
import List.Sorted
import Logic
import Nat
import Nat.Properties
import Product
import Sigma
import Sum
import Unit
import Vec
import WellFounded
```

## Test page

```agda
import Chapter.Test
```
