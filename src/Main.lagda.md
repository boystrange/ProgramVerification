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

```
import Chapters
```
