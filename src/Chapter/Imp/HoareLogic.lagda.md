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
Ass = State → Set

data Triple : Set₁ where
     [_]_[_] : Ass → Com → Ass → Triple
```
*Remark.* In the definition of the data type `Triple` we use square instead of curly braces because
the latter are reserved for implicit arguments in Agda. A peculiarity of `Triple` is
its type `Set₁` which is the least *universe* such that `Set = Set₀ : Set₁`. This is forced by Agda since
the type `Ass = State → Set`, and consequently the type `Set`, occurrs in negative position
in the type `Ass → Com → Ass → Triple` of `[_]_[_]`.

The treatment of universes is behind the scope of the present book: the interested reader is
referred to [Agda's documentation](https://agda.readthedocs.io/en/latest/language/universe-levels.html).
Luckily, the occurrences of `Set₁` here and in the definition of the inference system below can be
naively identified with `Set` without missing the content of the chapter.

Translating the partial correctness criterion into a definition, we say that
the triple `[ P ] c [ Q ]` is **valid** if for all `s, t ∈ State` whenever `P` holds of `s` and
`⦅ c , s ⦆` converges to `t`, `Q` holds of `t`. Formally, we define the following predicate: 

```
⊨_ : Triple → Set                         -- ⊨ is written \|=
⊨ [ P ] c [ Q ] = ∀ {s t} → P s → ⦅ c , s ⦆ ⇒ t → Q t
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
data ⊢_ : Triple → Set₁ where           -- ⊢ is written \|-

   H-Skip : ∀ {P}
          --------------------
          → ⊢ [ P ] SKIP [ P ]

   H-Loc : ∀ {P a x}
         → ⊢ [ (λ s → P (s [ x ::= aval a s ])) ] (x := a) [ P ]

   H-Comp : ∀ {P Q R c₁ c₂}
          → ⊢ [ P ] c₁ [ Q ]
          → ⊢ [ Q ] c₂ [ R ]
          ------------------------
          → ⊢ [ P ] c₁ :: c₂ [ R ]

   H-If : ∀ {P b c₁ Q c₂}
          → ⊢ [ (λ s → P s ∧ bval b s == true)  ] c₁ [ Q ]
          → ⊢ [ (λ s → P s ∧ bval b s == false) ] c₂ [ Q ]
          ------------------------------------------------
          → ⊢ [ P ] (IF b THEN c₁ ELSE c₂) [ Q ]

   H-While : ∀ {P b c}
          → ⊢ [ (λ s → P s ∧ bval b s == true) ] c [ P ]
          -----------------------------------------------------------
          → ⊢ [ P ] (WHILE b DO c) [ (λ s → P s ∧ bval b s == false) ]

   H-Conseq : ∀ {P Q P' Q' : Ass} {c}
          → (∀ s → P' s → P s)
          → ⊢ [ P  ] c [ Q  ]
          → (∀ s → Q s → Q' s)
          --------------------
          → ⊢ [ P' ] c [ Q' ]
```
Due to our definition of the type `Ass` of assertions, there are some differences
among the rules above and the original ones. In case of rule `H-Loc` Hoare's formulation was:

                               -------------------
                               {P[a/x]} x := a {P}

where `P[a/x]` is the result of the substitution of `x` by `a` in the formula `P`.
To understand rule `H-Loc`, suppose to extend the  *substitution lemma* in chapter
[Arithmetic and boolean expressions]({% link pages/Chapter.AexpBexp.md %})
to the syntax of formulas (if we had such things in our 
code, which we don't). Then we would have:

                    s ⊨ P[a/x]   if and only if  s [ x ::= aval a s] ⊨ P

where `s ⊨ P` means that `P` is true in the standard model of arithmetic if
the program variables in it are interpreted according to `s`. In our 
setting `P` has type `State → Set` and `s ⊨ P` is written `P s`; actually,
while it is unclear how to define `P[a/x] s` since 
we cannot substitute a variable in a predicate, writing
`P (s [ x ::= aval a s])` for `s [ x ::= aval a s] ⊨ P` makes perfect sense
in our formalism. 

There is a last step to take: `P (s[ x ::= aval a s])` has type `Set`,
but we need a predicate whose value is this expression as a function of `s ∈ State`,
hence the pre-condition of the rule `H-Loc` is the λ-expression
`λ s → P (s [ x ::= aval a s ])`. Similar remarks apply to rules `H-If` and `H-While`.

Finally rule `H-Conseq`, for *consequence*, corresponds to the original rule:

                       ⊨ P' → P    {P} c {Q}    ⊨ Q → Q'
                       ----------------------------------
                                   {P'} c {Q'}

Here we must encode the premises `⊨ P' → P` and `⊨ Q → Q'` as predicates.
In logic the meaning of `⊨ P' → P` is: for all `s` if `s ⊨ P'` then `s ⊨ P`,
which is immediately encoded into the Agda predicate `∀ s → P' s → P s`, that is
the first premise in the rule; the premise `⊨ Q → Q'` is treated similarly. 


## Soundness

Hoare Logic is intended to provide a tool to establish when a triple is valid.
To ensure that this is the case, we show that the system is *sound*  i.e. that only
valid triples are derivable. This is the content of `theorem-Hoare-sound` claiming the
implication

                    ∀ {P c Q} →  ⊢ [ P ] c [ Q ]  →  ⊨ [ P ] c [ Q ]

The strategy to prove the theorem is first to show that all instances of axioms `H-Skip` and `H-Loc`
are valid triples, which is immediate. Then the actual task in the proof is to show that
the remaining rules infer valid triples from valid ones instantiating the respective
premises. All in all, this a proof by structural induction on the derivation of
`⊢ [ P ] c [ Q ]`.

Going through the proof, we realise that the thesis is an easy consequence of the induction
hypotheses in all cases but in case of rule `H-While`, which deserves a more careful inspection.
In Hoare system the rule is written:

                                  {P ∧ b} c {P}
                            -------------------------
                            {P} WHILE b DO c {P ∧ ¬ b}

where `P` is the **loop invariant**, which is assumed to hold before executing the command
`WHILE b DO c` and to be preserved by the execution of the body `c` whenever
the condition of the guard `b` is true. From such hypotheses and the hypothesis
that the execution of `WHILE b DO c` terminates, the rule infers that the post-condition
of this loop is `P ∧ ¬ b`, where `¬ b` expresses the fact that for a `WHILE` command to
terminate the guard must be eventually false.

In our system the above rule is encoded by

           H-While : ∀ {P b c}
                   → ⊢ [ (λ s → P s ∧ bval b s == true) ] c [ P ]
                   -------------------------------------------------------------
                   → ⊢ [ P ] (WHILE b DO c) [ (λ s → P s ∧ bval b s == false) ]
 
To simplify the proof of the theorem, we begin with two lemmas stating respectively
that under the hypothesis that `[ (λ s → P s ∧ bval b s == true) ] c [ P ]` is valid,
the assertion `P` is a loop invariant for `WHILE b DO c` and that if its execution
terminates in a state `t` then `bval b t == false`.

```
lemma-Hoare-inv : ∀ {P : Ass} {s b c t} →
                  (∀{s' t'} → (P s' ∧ bval b s' == true) →
                               ⦅ c , s' ⦆ ⇒ t'
                               → P t') →
                  P s →
                  ⦅ WHILE b DO c , s ⦆ ⇒ t →
                  P t
                  
lemma-Hoare-inv {P} {s} {b} {c} {.s} hyp1 hyp2 (WhileFalse x) = hyp2
lemma-Hoare-inv {P} {s} {b} {c} {t} hyp1 hyp2
           (WhileTrue {.c} {.b} {.s} {s'} {s''} x hyp3 hyp4) = claim2 
     where
       claim1 = hyp1 {s} {s'} (hyp2 , x) hyp3               
       claim2 = lemma-Hoare-inv {P} {s'} {b} {c} {t}
                                  (hyp1 {_} {_}) claim1 hyp4

lemma-Hoare-loop-exit : ∀ {b c s t}
             → ⦅ WHILE b DO c , s ⦆ ⇒ t → bval b t == false 

lemma-Hoare-loop-exit (WhileFalse x) = x
lemma-Hoare-loop-exit (WhileTrue x hyp1 hyp2) =
                                  lemma-Hoare-loop-exit hyp2
```

Technically we observe the usage of implicit arguments in the proof of
`lemma-Hoare-inv` and in particular of dot patterns
Implicit arguments are necessary to distinguish
the states `s', s''` from `s`: indeed the formers are automatically generated by Agda
when splitting the hypothesis `⦅ WHILE b DO c , s ⦆ ⇒ s''` of the inductive case into
`⦅ c , s ⦆ ⇒ s'` and `⦅ WHILE b DO c , s' ⦆ ⇒ s''`, so that without passing the implicit arguments
to `WhileTrue` they are not in scope and hence inaccessible.

Dot patterns are constraints used by Agda to enforce the same binding of several occurrences
of a variable in a non linear pattern: for example the variable `{.c}` has to be bound to the
same command as the previous variable `{c}`. For explanations about dot patterns see
[Function Definitions - Dot patterns](https://agda.readthedocs.io/en/v2.5.2/language/function-definitions.html) in Agda documentation. 

We are eventually in place to prove `theorem-Hoare-sound` which is a corollary of
`lemma-Hoare-sound` that establishes a slightly stronger statement than the theorem
making the induction hypothesis to go through. 

```
lemma-Hoare-sound : ∀ {P c Q s t} →
             ⊢ [ P ] c [ Q ] → 
             P s → 
             ⦅ c , s ⦆ ⇒ t → 
             Q t

```
To facilitate the understanding of the proof we
intersperse the cases with some comments drown from the interactive construction of the proof itself.
As a first step in the proof we write

                     lemma-Hoare-sound hyp1 hyp2 hyp3 = ?

and then we hit `C-c C-c` twice splitting `hyp1 :  ⊢ [ P ] c [ Q ]` and
`hyp3 :  ⦅ c , s ⦆ ⇒ t`.

```
lemma-Hoare-sound H-Skip hyp2 Skip = hyp2

lemma-Hoare-sound H-Loc hyp2 Loc = hyp2

```
In cases of `H-Skip` and `H-Loc` the hypothesis `hyp2` in
the left-hand sides has the types `P s` and
`Q (s [ x ::= aval a s ])` respectively.
These are the same as the types of the respective right-hand sides, hence they
are both authomatically obtained typing `C-c C-a` while putting the cursor in the holes.
 
```

lemma-Hoare-sound (H-Comp hyp1 hyp4) hyp2 (Comp hyp3 hyp5) = IH2
      where
         IH1 = lemma-Hoare-sound hyp1 hyp2 hyp3
         IH2 = lemma-Hoare-sound hyp4 IH1 hyp5

```
In case of `H-Comp`, typing

          lemma-Hoare-sound (H-Comp hyp1 hyp4) hyp2 (Comp hyp3 hyp5) = ?

and then hitting `C-c C-,` with the cursor in the hole we obtain from Agda the reply
(omitting parameters that are not in scope): 

          Goal: Q t
          ———————————————————————————————————————————————————————
          hyp5 : ⦅ c₂ , s₂ ⦆ ⇒ t
          hyp3 : ⦅ c₁ , s ⦆ ⇒ s₂
          hyp2 : P s
          hyp4 : ⊢ [ Q₁ ] c₂ [ Q ]
          hyp1 : ⊢ [ P ] c₁ [ Q₁ ]

The induction hypothesis `lemma-Hoare-sound hyp1` is a proof of
`⊨  [ P ] c₁ [ Q₁ ]` that is applied to `hyp2 : P s` and to `hyp3 : ⦅ c₁ , s ⦆ ⇒ s₂`
yielding a proof `IH1 : Q₁ s₂`. On the other hand
the induction hypothesis `lemma-Hoare-sound hyp4` is a proof of
`⊨ [ Q₁ ] c₂ [ Q ]`, that when applied to `IH1 : Q₁ s₂` and `hyp5 : ⦅ c₂ , s₂ ⦆ ⇒ t`
returns a proof of `Q t` which is the goal. 


```
lemma-Hoare-sound (H-If hyp1 hyp4) hyp2 (IfTrue x hyp3) = thesis
      where

        IH = lemma-Hoare-sound hyp1
        thesis = IH (hyp2 , x) hyp3

lemma-Hoare-sound (H-If hyp1 hyp4) hyp2 (IfFalse y hyp3) = thesis
      where

        IH = lemma-Hoare-sound hyp4
        thesis = IH (hyp2 , y) hyp3
```

Case `H-If` is split into two subcases according to 
the value of `b` from the command `IF b THEN c₁ ELSE c₂` in
the third hypothesis. By asking Agda about the context by means of
`C-c C-,` we get 

          Goal: Q t
          ——————————————————————————————————————————————————————
          hyp3 : ⦅ c₁ , s ⦆ ⇒ t
          x    : bval b s == true
          hyp2 : P s
          hyp4 : ⊢ [ (λ s₁ → P s₁ ∧ bval b s₁ == false) ] c₂ [ Q ]
          hyp1 : ⊢ [ (λ s₁ → P s₁ ∧ bval b s₁ == true) ] c₁ [ Q ]

In case of `(IfTrue x hyp3) : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t`
the induction hypothesis
`IH = lemma-Hoare-sound hyp1 : ⊨ [ (λ s₁ → P s₁ ∧ bval b s₁ == true) ] c₁ [ Q ]`
is applied to `(hyp2 , x) : P s ∧ bval b s == true` and to `hyp3 : ⦅ c₁ , s ⦆ ⇒ t`
yielding a proof `thesis : Q t` as desired.

The case `(IfFalse y hyp3) : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t`, where
`hyp3 : ⦅ c₂ , s ⦆ ⇒ t` and
`y : bval b s == false` is similar, using the induction
hypothesis `IH = lemma-Hoare-sound hyp4`.

```

lemma-Hoare-sound {P} {_} {_} {s} {t}
                  (H-While {_} {b} hyp1) hyp2 hyp3 = Pt , b-false
      where

        Pt : P t
        Pt = lemma-Hoare-inv (lemma-Hoare-sound hyp1 ) hyp2 hyp3 

        b-false : bval b t == false
        b-false = lemma-Hoare-loop-exit hyp3

```

Case `H-While` is the most interesting one. Starting with

          lemma-Hoare-sound {P} {_} {_} {s} {t}
                  (H-While {.P} {b} hyp1) hyp2 hyp3 = ?

and typing `C-c C-l` and then `C-c C-,` with the cursor in the hole we get the context:

          Goal: P t ∧ bval b t == false
          ———————————————————————————————————————————————————————
          hyp3 : ⦅ WHILE b DO c , s ⦆ ⇒ t
          hyp2 : P s
          hyp1 : ⊢ [ (λ s₁ → P s₁ ∧ bval b s₁ == true) ] c [ P ]

Since the goal is a conjunction, putting the cursor in the hole and typing `C-c C-r` to refine
Agda's guess about the filling of the hole, we get a pair of holes `{!!} , {!!}`; in the first hole
it is expected a proof of `P t`, which is called `Pt` in the above proof, and in the second hole
a proof of `bval b == false` is required, which is called `b-false`.

Now, by passing the induction hypothesis
`lemma-Hoare-sound hyp1 : ⊨ [ (λ s₁ → P s₁ ∧ bval b s₁ == true) ] c [ P ]` to the lemma
`lemma-Hoare-inv` and then the result to `hyp2` and to `hyp3` we get a proof of the fact
that `P` is an invariant of the command `WHILE b DO c`, hence it holds for the final
state `t` whenever `⦅ WHILE b DO c , s ⦆ ⇒ t`; therefore we have established that `P t`
holds as required.

On the other hand applying `lemma-Hoare-loop-exit` to `hyp3 : ⦅ WHILE b DO c , s ⦆ ⇒ t`
we obtain a proof `b-false : bval b t == false` which ends the proof of this case. 

```

lemma-Hoare-sound {_} {_} {_} {s} {t}
                               (H-Conseq x hyp1 y) hyp2 hyp3 = ths
      where

        P₁s = x s hyp2
        IH  = lemma-Hoare-sound hyp1
        Q₁t = IH P₁s hyp3
        ths = y t Q₁t
```
In the case `H-Conseq` we have the context:

          Goal: Q t
          —————————————————————————————————————————————————————
          hyp3 : ⦅ c , s ⦆ ⇒ t
          hyp2 : P s
          y    : (s₁ : State) → Q₁ s₁ → Q s₁
          hyp1 : ⊢ [ P₁ ] c [ Q₁ ]
          x    : (s₁ : State) → P s₁ → P₁ s₁

Then the induction hypothesis `lemma-Hoare-sound hyp1 : ⊨ [ P₁ ] c [ Q₁ ]` can be easily
combined with `P₁s = x s hyp2 : P₁ s` and `Q₁t = IH P₁s hyp3 : Q₁ t` establishing
the thesis `ths = y t Q₁t : Q t` as desired. 

Eventually we conclude:

```
theorem-Hoare-sound : ∀ {P c Q} →
            ⊢ [ P ] c [ Q ] → ⊨ [ P ] c [ Q ]

theorem-Hoare-sound hyp = lemma-Hoare-sound hyp

```
