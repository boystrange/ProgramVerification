---
title: Main
---

This module imports **everything**, so that Agda can generate the
markdown files for all of the sources.

## Structure

1. definizione di funzioni in Agda, uso dell'ambiente interattivo
2. inductive types, pattern matching (Bool, not/and/or)
3. Uguaglianza e refl, freccia dipendente (teoremi sui booleani, not
   involuzione, and/or commutativi, ecc.)
4. recursive inductive types, recursive functions (Nat, somma,
   moltiplicazione)
5. uso di refl su numeri naturali, prove per induzione strutturale
   (associatività, commutatività, distributività, ecc.)
6. Funzioni polimorfe e argomenti impliciti (identità, flip,
   composizione funzionale)
7. Polymorphic inductive types (liste, concatenazione, reverse, fast
   reverse).
8. Propositional logic (connettivi e costanti della logica
   proposizionale, iff, negazione)
9. existential quantifier
10. defining predicates, type-level computations, inductive families
   (even, equality, less-than, list permutations)
11. Extrinsic vs intrinsic verification (insertion sort)
12. Mutually recursive data types with invariants (red black trees)
13. well-founded relations and termination (euclidean division)
14. non-structural recursion with measures (quick sort)

```
import Chapters
```
