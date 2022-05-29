---
title: Main
---

This module imports **everything**, so that Agda can generate the
markdown files for all of the sources.

```agda
-- LECTURE 1
import Demo
import Setup
import Lambda
import Interactive

-- insertion sort (intrinsic and extrinsic)
import InsertionSort

-- non-structural recursion using measures, intrinsic verification
import QuickSort

-- Red black trees (definition of data structure enforces
-- invariants, mutual induction and mutual recursion, <= reasoning)
import RedBlackTree

-- Regular expression matching (inference systems)
import Regex

-- Euclidean division (termination, well founded recursion)

-- LIBRARY
import Library

-- TEST PAGE
import TestPage
```
