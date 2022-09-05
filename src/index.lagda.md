---
title: Summary
---

<!--
```
module index where
```
-->

## Chapters

### Preamble

```
import Chapter.Preamble.Demo
import Chapter.Preamble.Setup
```

### Functions and data

```
import Chapter.Intro.Lambda
import Chapter.Intro.Bool
import Chapter.Intro.BoolProperties
import Chapter.Intro.NaturalNumbers
import Chapter.Intro.Polymorphism
import Chapter.Intro.Lists
```

### Constructive logic

```
import Chapter.Logic.Connectives
import Chapter.Logic.Negation
import Chapter.Logic.Existential
import Chapter.Logic.Predicates
import Chapter.Logic.Equality
import Chapter.Logic.LessThan
```

### Verification of functional programs

```
import Chapter.Fun.SortedLists
import Chapter.Fun.ExtrinsicInsertionSort
import Chapter.Fun.IntrinsicInsertionSort
import Chapter.Fun.RedBlackTree
import Chapter.Fun.RegularExpressions
import Chapter.Fun.Division
import Chapter.Fun.QuickSort
```

### Verification of imperative programs

```
import Chapter.Imp.AexpBexp
import Chapter.Imp.BigStep
import Chapter.Imp.SmallStep
import Chapter.Imp.HoareLogic
import Chapter.Imp.HoareLogicExample
import Chapter.Imp.HoareLogicSoundness
```

## Mini Agda library

```
import Bool
import Equality
import Equality.Reasoning
import Fun
import LessThan
import LessThan.Alternative
import LessThan.Reasoning
import List
import List.Permutation
import List.Properties
import List.Sorted
import Logic
import Logic.Laws
import Nat
import Nat.Properties
import WellFounded
```

## Summary of Emacs shortcuts

| Command       | Action                                           |
|---------------|--------------------------------------------------|
| `C-c C-l`     | Load the current file                            |
| `C-c C-d`     | Enter an expression and show its type            |
| `C-c C-n`     | Enter an expression and normalize it             |
| `C-c C-c`     | Enter an argument an perform case analysis on it |
| `C-c C-,`     | Show goal and context                            |
| `C-c C-f`     | Move forward to the next goal                    |
| `C-c C-b`     | Move backward to the previous goal               |
| `C-c C-SPACE` | Fill the hole with the provided expression       |

## Copyright

The course material in this site has been posted for your personal
educational use only. Copying course material from this site for
distribution (e.g. uploading material to a commercial third-party or
public website, or otherwise sharing these materials with people who
are not part of the class) may be a violation of Copyright law. If
you have questions regarding the use of materials from this site,
please contact the instructor.

## References

* Ana Bove and Peter Dybjer, [Dependent Types at Work](https://doi.org/10.1007/978-3-642-03153-3_2), 2008.
* David Darais, course on [Software Verification](http://david.darais.com/courses/2018-08-cs295A/), 2018.
* Samuel Mimram, [Program = Proof](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf), 2020.
* Peter Selinger, [lectures on Agda](https://www.mathstat.dal.ca/~selinger/agda-lectures/), 2021.
* Aaron Stump, [Verified Functional Programming in Agda](http://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?cPath=24&products_id=908), 2016.
* Phil Wadler, Wen Kokke and Jeremy G. Siek, [Programming Language Foundations in Agda](https://plfa.github.io), 2019.
