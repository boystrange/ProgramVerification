---
title: "Hoare Logic for verification of IMP programs" 
---


```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Imp.HoareLogic where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning

open import Chapter.Imp.AexpBexp
open import Chapter.Imp.BigStep

```


The goal of *program verification* is to check whether programs satisfy their
specifications, which nowdays is called *functional correctness* and
*compliance* of programs w.r.t. their *contracts*.

The formalization of the operational semantics of IMP lays the ground for
precise reasoning e.g. about implementations of IMP intepreters,
like that one provided by the small-step semantics in chapter
[Small-step operational semantics]({% link pages/Chapter.Imp.SmallStep.md %}),
or of a compiler as described in chapter 8 of Nipkow and Klein's book.
However, reasoning about single programs using the operational semantics,
albeit possible in principle, is quite awkward in practice.
 
In the late 60s, building on Robert Floyd's idea to decorate flowcharts with logical formulas
to reason about programs,
Tony Hoare proposed a logical system to derive formulas
of the shape `{P} c {Q}` he called **triples**. A triple is made of a command `c` and
two formulas `P, Q` of first order arithmetic, called **pre-condition** and
**post-condition** respectively. The meaning of such triples is
the so called **partial correctness** criterion:

     A command (program) c is partially correct w.r.t the specification
     with pre-condition P and post-condition Q if whenever P is true
     before the execution of c and such execution terminates,
     Q is true afterwards

Observe that the termination of the execution of `c` is not ensured by the truth of `P`,
so that when this is not the case the triple `{P} c {Q}` vacuously holds.

A direct formalization of triples and Hoare Logic with Agda involves the definition of
the language of arithmetic and of its semantics. Following the technique in
chapter 12 of Nipkow and Klein's book, we use instead a *shallow embedding* of triples into Agda,
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


## The system of Hoare Logic

Hoare Logic is an axiomatization of the notion of **partially correct program**, 
consisting of a formal system of inference rules whose judgments are triples plus
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
          ---------------------------------------------------------- 
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
[Arithmetic and boolean expressions]({% link pages/Chapter.Imp.AexpBexp.md %})
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

## Derived rules

```
H-Str :    ∀ {P Q P′ : Assn} {c}
            -> (∀ s -> P′ s -> P s)
            -> |- [ P  ] c [ Q  ]
            ------------------------
            -> |- [ P′ ] c [ Q ]

H-Str {P}{Q}{P′}{c} hyp1 hyp2 =
            H-Conseq {P}{Q}{P′}{Q}{c} hyp1 hyp2 (λ s -> λ x -> x)


H-Weak :  ∀ {P Q Q′ : Assn} {c}
          -> |- [ P  ] c [ Q  ]
          -> (∀ s -> Q s -> Q′ s)
          ------------------------
          -> |- [ P ] c [ Q′ ]

H-Weak {P}{Q}{Q′}{c} hyp1 hyp2 =
            H-Conseq {P}{Q}{P}{Q′}{c} (λ s -> λ x -> x) hyp1 hyp2

H-While' :  ∀ {P b c Q}
          -> |- [ (λ s -> P s ∧ bval b s == true) ] c [ P ]
          -> (∀ s -> (P s ∧ bval b s == false) -> Q s)
          -> |- [ P ] (WHILE b DO c) [ Q ]

H-While' hyp1 hyp2 = H-Weak (H-While hyp1) hyp2
```

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

The next example is the proof of `|- {X = 1} Z := X ; Y := Z {Y = 1}` where `;`
is written `::` in our formalism: 

    |-  [ V X ==' N 1 ]
          (Z := V X) :: (Y := V Z)
        [ V Y ==' N 1 ]

This case can be treated by applying the composition rule `H-Comp` to `pr0-0` and `pr0-1` below:
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

### Selection

Let's consider the triple `{⊤} IF X < Y THEN Z := Y ELSE Z := X {Z = max(X,Y)}`, where `⊤` is the trivial pre-condition
which is true of any state. To formalize this triple in our setting, we first introduce the trivial assertion `⊤' ∈ Assn`
that is true of any `s ∈ State`,
and the predicate `max' a₁ a₂ a₃ ∈ Assn` with `a₁ a₂ a₃ ∈ Aexp` that is true of `s ∈ State`
if `aval a₃ s ∈ ℕ` is the maximum among `aval a₁ s` and `aval a₂ s`: 
```
⊤' : Assn
⊤' s = ⊤

max' : Aexp -> Aexp -> Aexp -> Assn
max' a₁ a₂ a₃ = λ s -> max (aval a₁ s) (aval a₂ s) == aval a₃ s
```
where `max : ℕ -> ℕ -> ℕ` is the maximum function defined in the library `Nat.agda`.
Now we can express the goal of our proof as follows:

    |- [ ⊤' ]
         IF (Less (V X) (V Y)) THEN (Z := V Y) ELSE (Z := V X)
       [ max' (V X) (V Y) (V Z) ]
 
Here we expect to use rule `H-If` whose premises are:

    H1  |- [ (λ s -> ⊤' s ∧ (bval (Less (V X) (V Y)) s == true)) ]
             Z := V Y
           [ max' (V X) (V Y) (V Z) ]

    H2  |- [ (λ s -> ⊤' s ∧ (bval (Less (V X) (V Y)) s == false)) ]
             Z := V X
           [ max' (V X) (V Y) (V Z) ]

Toward proving the first hypothesis `H1` let us show that if
`|- {max(X, Y) = Y} Z := Y {max(X, Y) = Z}`:
```
pr1-1 : |- [ max' (V X) (V Y) (V Y) ]
           Z := V Y
           [ max' (V X) (V Y) (V Z) ]
           
pr1-1 = H-Loc {max' (V X) (V Y) (V Z)} {V Y} {Z} 
```
Next we show that if  `X < Y` and we assign `Z := Y` then `max(X, Y) = Z`:  

```
less-max : ∀(n m : ℕ) -> n <ℕ m == true -> max n m == m
 
less-max zero m hyp = refl
less-max (succ n) (succ m) hyp = cong succ (less-max n m hyp)

less-max' : ∀(a a' : Aexp) -> (s : State) ->
               bval (Less a a') s == true -> max' a a' a' s
               
less-max' a a' s hyp = less-max (aval a s) (aval a' s) hyp

pr1-2 : ∀ s -> (⊤' s ∧ (bval (Less (V X) (V Y)) s == true)) ->
               max' (V X) (V Y) (V Y) s
               
pr1-2 s (x , y) = less-max' (V X) (V Y) s y
```
In `pr1-2` we have considered the hypothesis `∀ s -> ⊤' s ∧ (bval (Less (V X) (V Y)) s == true`
instead of its equivalent (and more natural) `∀ s -> (bval (Less (V X) (V Y)) s == true`
because it is exactly
the pre-condition of `H1` we are trying to prove; on the other
hand the consequence `max' (V X) (V Y) (V Y) s` of `pr1-2` matches with the pre-condition
of `pr1-1`, where
the arbitrary `s` is omitted because we have just the predicate `max' (V X) (V Y) (V Y)`.
This suggests that to conclude `H1` we can use the rule `H-Str` applied to `pr1-2` and `pr1-1`: 
```
H1 : |- [ (λ s -> ⊤' s ∧ (bval (Less (V X) (V Y)) s == true)) ]
        Z := V Y
        [ max' (V X) (V Y) (V Z) ]
           
H1 = H-Str pr1-2 pr1-1
```
The proof of `H2` follows a similar pattern, this time considering the case when
`bval (Less (V X) (V Y)) s == false`:
```
geq-max : ∀(n m : ℕ) -> n <ℕ m == false -> max n m == n

geq-max zero zero hyp = refl
geq-max (succ n) zero hyp = refl
geq-max (succ n) (succ m) hyp = cong succ (geq-max n m hyp)

geq-max' : ∀(a a' : Aexp) -> (s : State) ->
           bval (Less a a') s == false -> max' a a' a s

geq-max' a a' s hyp = geq-max (aval a s) (aval a' s) hyp

pr1-3 : |- [ max' (V X) (V Y) (V X) ]
           Z := V X
           [ max' (V X) (V Y) (V Z) ]
           
pr1-3 = H-Loc {max' (V X) (V Y) (V Z)} {V X} {Z}

pr1-4 : ∀ s -> (⊤' s ∧ (bval (Less (V X) (V Y)) s == false)) ->
             max' (V X) (V Y) (V X) s
             
pr1-4 s (x , y) = geq-max' (V X) (V Y) s y

H2 : |- [ (λ s -> ⊤' s ∧ (bval (Less (V X) (V Y)) s == false)) ]
        Z := V X
        [ max' (V X) (V Y) (V Z) ]
           
H2 = H-Str pr1-4 pr1-3
```
Evenually we apply rule `H-If` to `H1` and `H2`, and we conclude:
```
pr1-5 : |- [ ⊤' ]
          IF (Less (V X) (V Y)) THEN (Z := V Y) ELSE (Z := V X)
          [ max' (V X) (V Y) (V Z) ]

pr1-5 = H-If H1 H2
```

## Exercise 

To abbreviate some assertions, we add the following "conjunction" operator:
```
_∧'_ : Assn -> Assn -> Assn
P ∧' Q = λ s -> P s ∧ Q s
```
Then prove:

    |- [ (V X ==' N 1) ∧' (V Y ==' N 2) ]
         (Z := V X) :: ((X := V Y) :: (Y := V Z))
       [ (V Y ==' N 1) ∧' (V X ==' N 2) ]


```
pr1 : |- [ (V Z ==' N 1) ∧' (V X ==' N 2) ]
         Y := V Z
         [ (V Y ==' N 1) ∧' (V X ==' N 2) ]
         
pr1 = H-Loc { (V Y ==' N 1) ∧' (V X ==' N 2) } {V Z} {Y}

pr2 : |- [ (V Z ==' N 1) ∧' (V Y ==' N 2) ]
         X := V Y
        [ (V Z ==' N 1) ∧' (V X ==' N 2) ]
         
pr2 =  H-Loc { (V Z ==' N 1) ∧' (V X ==' N 2) } {V Y} {X} 

pr3 : |- [ (V X ==' N 1) ∧' (V Y ==' N 2) ]
         Z := V X
        [ (V Z ==' N 1) ∧' (V Y ==' N 2) ]
        
pr3 =  H-Loc { (V Z ==' N 1) ∧' (V Y ==' N 2) } {V X} {Z}

pr4 : |- [ (V Z ==' N 1) ∧' (V Y ==' N 2) ]
        (X := V Y) :: (Y := V Z)
        [ (V Y ==' N 1) ∧' (V X ==' N 2) ]
        
pr4 = H-Comp { (V Z ==' N 1) ∧' (V Y ==' N 2) }
            { (V Z ==' N 1) ∧' (V X ==' N 2) }
            { (V Y ==' N 1) ∧' (V X ==' N 2) }
            { X := V Y } { Y := V Z }
            pr2 pr1

pr5 : |- [ (V X ==' N 1) ∧' (V Y ==' N 2) ]
        (Z := V X) :: ((X := V Y) :: (Y := V Z))
        [ (V Y ==' N 1) ∧' (V X ==' N 2) ]

pr5 = H-Comp {(V X ==' N 1) ∧' (V Y ==' N 2)}
             {(V Z ==' N 1) ∧' (V Y ==' N 2)}
             {(V Y ==' N 1) ∧' (V X ==' N 2)}
             {Z := V X}
             {(X := V Y) :: (Y := V Z)}
             pr3 pr4
```
{:.solution} 
