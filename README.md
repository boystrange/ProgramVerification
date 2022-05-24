# Program Verification in Agda

* 42 hours
* 21 lectures
* Inspiration from [Peter Selinger's lectures on
  Agda](https://www.mathstat.dal.ca/~selinger/agda-lectures/)
* [PLFA](https://plfa.github.io)
* [Agda](https://agda.readthedocs.io/en/latest/)
* [Agda standard library](https://agda.github.io/agda-stdlib/)

## Program

1. Introduction
   1. Demo
   2. Agda setup
   3. First steps with Agda, types, terms, typing rules
   4. Functions with multiple arguments, currying
2. Simply typed λ calculus
   1. Syntax
   2. Typing rules
   3. The Curry-Howard isomorphism
3. Inductive data types
   1. Boolean values, functions on boolean values, conjunction,
      disjunction, negation, pattern matching
   2. Natural numbers, functions on natural numbers, sum,
      multiplication
   3. builtin notation?
3. Types as arguments
4. Properties of lists
   1. Representation of lists
   2. Notable functions on lists
   3. Properties
   4. Sorting algorithms (insertion sort, quick sort?)
   5. Extrinsic vs intrinsic verification
5. Binary trees
   1. Representation
   2. Binary search trees (vedi articolo di Bove)
6. Inductive families (types depending on terms)
   1. Fin
   2. Vec
   3. Equality and equational reasoning, `rewrite`
   4. Matrices, faster Fibonacci
7. Logic
   1. Conjunction and disjunction
   2. Negation
   3. True and False
   4. Existential quantification, there exist infinitely many
      even/prime numbers
   5. Decidability
8. Imperative programs
   1. IMP
   2. Reduction, big step, small step, termination, determinism
   3. Compilation
