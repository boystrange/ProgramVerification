---
title: "Hoare Logic for program verification"
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Imp.HoareLogic where

open import Bool
open import Nat
open import Nat.Properties
open import Logic
open import Logic.Laws
open import Equality
open import Equality.Reasoning

open import Chapter.Imp.AexpBexp
open import Chapter.Imp.BigStep

```
-->

The goal of *program verification* is to check whether programs satisfy their
specifications, which nowdays is called *functional correctness* and
*compliance* of programs w.r.t. their *contracts*.

The formalization of the operational semantics of IMP lays the ground for
precise reasoning e.g. about implementations of IMP intepreters,
like that one provided by the small-step semantics in chapter
[Small-step operational semantics]({% link pages/Chapter.SmallStep.md %}),
or of a compiler as described in chapter 8 of Nipkow and Klein's book.
However, reasoning about single programs using the operational semantics,
albeit possible in principle, is quite awkward in practice.
 
In the late 60s, building on Robert Floyd's idea to decorate flowcharts with logical formulas
to reason about programs,
Tony Hoare proposed a logical system to derive formulas
of the shape `{P} c {Q}` he called a **triple**, made of a command `c`and
two formulas `P, Q` of first order arithmetic, called **pre-condition** and
**post-condition** respectively. The meaning of such triples is
the so called *partial correctness* criterion:

     A command (program) c is partially correct w.r.t the specification
     with pre-condition P and post-condition Q if whenever P is true
     before the execution of c and such execution terminates,
     Q is true afterwards

Observe that the termination of the execution of `c` is not ensured by the truth of `P`,
so that when this is not the case the triple `{P} c {Q}` vacuously holds.

A direct formalization of triples and Hoare Logic with Agda involves the definition of
the language of arithmetic and of its semantics. Following the technique in
chapter 12 of Nipkow and Klein's book, we use instead a shallow embedding of triples into Agda,
much as we have done for the IMP language until now. Then
pre and post-conditions, named **assertions** in Hoare's words, are formalized as Agda
predicates of states:
 
```
Assn = State -> Set

data Triple : Set₁ where
     [_]_[_] : Assn -> Com -> Assn -> Triple
```
*Remark.* In the definition of the data type `Triple` we use square instead of curly braces because
the latter are reserved for implicit arguments in Agda. A peculiarity of `Triple` is
its type `Set₁` which is the least *universe* such that `Set = Set₀ : Set₁`. This is forced by Agda since
the type `Assn = State -> Set`, and consequently the type `Set`, occurrs in negative position
in the type `Assn -> Com -> Assn -> Triple` of `[_]_[_]`.

The treatment of universes is behind the scope of the present book: the interested reader is
referred to [Agda's documentation](https://agda.readthedocs.io/en/latest/language/universe-levels.html).
Luckily, the occurrences of `Set₁` here and in the definition of the inference system below can be
naively identified with `Set` without missing the content of the chapter.

Translating the partial correctness criterion into a definition, we say that
the triple `[ P ] c [ Q ]` is **valid** if for all `s, t ∈ State` whenever `P` holds of `s` and
`⦅ c , s ⦆` converges to `t`, `Q` holds of `t`. Formally, we define the following predicate: 

```
|=_ : Triple -> Set
|= [ P ] c [ Q ] = ∀ {s t} -> P s -> ⦅ c , s ⦆ ⇒ t -> Q t
```

## The system of Hoare Logic

Hoare Logic is an axiomatization of the notion of valid triple, consisting of
a formal system of inference rules whose judgments are triples plus
logical formulas to make arithmetics available when reasoning about IMP
programs. The original formulation of the system
can be found e.g. in chapter 6 of Winskel's book and
in chapter 12 of Nipkow and Klein's book. A quick reference is
[Wikipedia - Hoare Logic](https://en.wikipedia.org/wiki/Hoare_logic).
 
We represent the rules of Hoare Logic in Agda via the constructors of the following data type:

```
data |-_ : Triple -> Set₁ where 

   H-Skip : ∀ {P}
          ----------------------
          -> |- [ P ] SKIP [ P ]

   H-Loc : ∀ {P a x}
          -> |- [ (λ s -> P (s [ x ::= aval a s ])) ] (x := a) [ P ]

   H-Comp : ∀ {P Q R c₁ c₂}
          -> |- [ P ] c₁ [ Q ]
          -> |- [ Q ] c₂ [ R ]
          --------------------------
          -> |- [ P ] c₁ :: c₂ [ R ]

   H-If : ∀ {P b c₁ Q c₂}
          -> |- [ (λ s -> P s ∧ bval b s == true)  ] c₁ [ Q ]
          -> |- [ (λ s -> P s ∧ bval b s == false) ] c₂ [ Q ]
          ---------------------------------------------------
          -> |- [ P ] (IF b THEN c₁ ELSE c₂) [ Q ]

   H-While : ∀ {P b c}
          -> |- [ (λ s -> P s ∧ bval b s == true) ] c [ P ]
          ---------------------------------------------------------------
          -> |- [ P ] (WHILE b DO c) [ (λ s -> P s ∧ bval b s == false) ]

   H-Conseq : ∀ {P Q P' Q' : Assn} {c}
          -> (∀ s -> P' s -> P s)
          -> |- [ P  ] c [ Q  ]
          -> (∀ s -> Q s -> Q' s)
          -----------------------
          -> |- [ P' ] c [ Q' ]
```
Due to our definition of the type `Assn` of assertions, there are some differences
among the rules above and the original ones. In case of rule `H-Loc` Hoare's formulation was:

                               -------------------
                               {P[a/x]} x := a {P}

where `P[a/x]` is the result of the substitution of `x` by `a` in the formula `P`.
To understand rule `H-Loc`, suppose to extend the  *substitution lemma* in chapter
[Arithmetic and boolean expressions]({% link pages/Chapter.AexpBexp.md %})
to the syntax of formulas (if we had such things in our 
code, which we don't). Then we would have:

                    s |= P[a/x]   if and only if  s [ x ::= aval a s] |= P

where `s |= P` means that `P` is true in the standard model of arithmetic if
the program variables in it are interpreted according to `s`. In our 
setting `P` has type `State -> Set` and `s |= P` is written `P s`; actually,
while it is unclear how to define `P[a/x] s` since 
we cannot substitute a variable in a predicate, writing
`P (s [ x ::= aval a s])` for `s [ x ::= aval a s] |= P` makes perfect sense
in our formalism. 

There is a last step to take: `P (s[ x ::= aval a s])` has type `Set`,
but we need a predicate whose value is this expression as a function of `s ∈ State`,
hence the pre-condition of the rule `H-Loc` is the λ-expression
`λ s -> P (s [ x ::= aval a s ])`. Similar remarks apply to rules `H-If` and `H-While`.

Finally rule `H-Conseq`, for *consequence*, corresponds to the original rule:

                       |= P' -> P    {P} c {Q}    |= Q -> Q'
                       -------------------------------------
                                    {P'} c {Q'}

Here we must encode the premises `|= P' -> P` and `|= Q -> Q'` as predicates.
In logic the meaning of `|= P' -> P` is: for all `s` if `s |= P'` then `s |= P`,
which is immediately encoded into the Agda predicate `∀ s -> P' s -> P s`, that is
the first premise in the rule; the premise `|= Q -> Q'` is treated similarly. 

## Examples


### Assignment
 
Let us start with the example `|- {X = 1} Z := X {Z = 1}`, which in our formalism reads:

                       |- [ V X ==' N 1 ]
                          Z := V X
                          [ V Z ==' N 1 ]

where `a₁ ==' a₂` is the predicate of `a₁, a₂ ∈ Aexp` which holds w.r.t. `s ∈ State` if
`aval a₁ s == aval a₂ s`:

```
_=='_ : Aexp -> Aexp -> Assn
a ==' a' = λ s -> aval a s == aval a' s
```
We observe that the pre-condition `X = 1` is just the result of substituting `Z` for `X` in the
post-condition `Z = 1`; since the command `Z := X` always terminates and assigns the value of `X`
to `Z`, which according to the pre-condition is `1`,
the triple is clearly valid, and indeed in our formalism it can be derived by means of rule `H-Loc`:

```
pr0-0 : |- [ V X ==' N 1 ]
           Z := V X
           [ V Z ==' N 1 ]

pr0-0 = H-Loc {V Z ==' N 1} {V X} {Z}
```

### Composition

The next example is the proof of `|- {X = 1} Z := X ; Y := Z {Y = 1}` where `;` is written `::` in our setting:

                       |-  [ V X ==' N 1 ]
                           (Z := V X) :: (Y := V Z)
                           [ V Y ==' N 1 ]

This case can be treated by applying the composition rule `H-Comp` to the proofs `pr0-0` and to
```
pr0-1 : |- [ V Z ==' N 1 ]
           Y := V Z
           [ V Y ==' N 1 ]

pr0-1 = H-Loc  {V Y ==' N 1} {V Z} {Y}
```
Eventually we obtain the proof:
```
pr0-2 : |- [ V X ==' N 1 ]
           (Z := V X) :: (Y := V Z)
           [ V Y ==' N 1 ]

pr0-2 = H-Comp {V X ==' N 1}
              {V Z ==' N 1}
              {V Y ==' N 1}
              {Z := V X}
              {Y := V Z}
              pr0-0 pr0-1              
```
