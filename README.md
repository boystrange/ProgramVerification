# Program Verification in Agda

* 42 hours
* 21 lectures
* Inspiration from [Peter Selinger's lectures on
  Agda](https://www.mathstat.dal.ca/~selinger/agda-lectures/)
* [PLFA](https://plfa.github.io)
* [Agda](https://agda.readthedocs.io/en/latest/)
* [Agda standard library](https://agda.github.io/agda-stdlib/)

## Structure

1. Defining Agda functions, using the interactive environment
2. Inductive types, pattern matching (Bool, not/and/or)
3. Using equaility and `refl`, dependent arrow type (properties of
   booleans, not is an involution, and/or are commutative, etc.)
4. Recursive inductive types, recursive functions (natural numbers,
   addition, multiplication, etc.)
5. Using equality and `refl` on natural numbers, proof by structural
   induction (associativity, commutativity, distributivity, etc.)
6. Polymorphic functions and implicit arguments (identity, `flip`,
   function composition)
7. Polymorphic inductive types (lists, concatenation and `reverse`,
   fast reverse and proof of equivalence with `reverse`).
8. Propositional logic (connectives and constants of propositional
   logic, if and only if)
9. Negation and decidability (== is decidable for Bool, Nat, lists, etc.)
10. Existential quantification
11. Defining predicates, type-level computations, inductive families
   (evenness predicate, equality, less-than, list permutations)
12. Extrinsic vs intrinsic verification (insertion sort)
13. Mutually recursive data types with invariants (red black trees)
14. Well-founded relations and termination (euclidean division)
15. Non-structural recursion with measures (quick sort)

## Bootstrap

1. `bundle config set --local path 'vendor/bundle'`
2. `bundle install`

## Running

1. In a terminal run `make` from the root directory to launch
   Jekyll, then click on the provided address to start up the
   browser.
2. In another terminal run `./watch.sh` from the sub-folder
   `src`. This will watch for changes in the literate Agda sources
   and invoke Agda to generate the corresponding `.md` and `.html`
   files.
