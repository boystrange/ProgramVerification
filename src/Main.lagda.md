---
title: Main
---

This module imports **everything**, so that Agda can generate the
markdown files for all of the sources.

## Structure

1. λ calculus, definizione di funzioni in Agda, combinatori (S, K,
   I), prodotto
2. inductive types: definizione di Bool, pattern matching,
   definizione di connettivi
3. il tipo dell'uguaglianza, uso di refl (far vedere che si usa la
   normalizzazione per determinare se due valori sono uguali),
   teoremi, freccia dipendente
4. inductive types: definizione di Nat, funzioni ricorsive (somma,
   moltiplicazione)
5. uso di refl su numeri naturali, prove per induzione strutturale
   (associatività, commutatività, ecc.)
6. altri tipi di dato induttivi: Product, Sum, Empty, Unit
7. Logica proposizionale, interpretazione BHK dà le regole di
   introduzione ma non quelle di eliminazione, sistema NJ? Possiamo
   mostrare come si codifica NJ con i tipi di dato così introdotti?
8. Negazione
9. Inductive families: tipi che dipendono da valori. Even, Equality,
   LessThan, dimostrare che Even è corretto/completo rispetto a
   predicato "essere multiplo di 2", dimostrare che LessThan è
   corretto/completo rispetto a predicato "k + m"
10. Fin e Vec?
11. Polymorphic inductive types: liste e operazioni sulle liste,
    risultati sulle liste.
12. Predicati sulle liste


## Chapters

```agda
import Chapter.Demo
import Chapter.Setup
import Chapter.Lambda
import Chapter.Interactive

import Chapter.Bool
import Chapter.BoolProperties

-- Booleans, first theorems using equality

-- Empty, Unit, Product, Sum

-- Logic, Curry-Howard isomorphism

-- Dependent arrow type, dependent product

-- Natural numbers, properties using equalities

-- Inductive families (being even, being equal)

-- Lists, properties

-- insertion sort (intrinsic and extrinsic)
import Chapter.InsertionSort

-- Red black trees (embedding invariants in the definition of data structure,
-- mutual induction and mutual recursion, <= reasoning)
import Chapter.RedBlackTree

-- Regular expression matching (inference systems)
import Chapter.Regex

-- Euclidean division (termination, well founded relations)
import Chapter.Division

-- non-structural recursion using measures
import Chapter.QuickSort
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
