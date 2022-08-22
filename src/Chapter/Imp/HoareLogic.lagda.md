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
 
Building on Robert Floyd's idea to decorate flowcharts with logical formulas,
Tony Hoare introduced in the late 60s a logical system to derive formulas
of the shape `{P}c{Q}` he called a **triple**, made of a command `c`and
two formulas `P, Q` of first order arithmetic, called **pre-condition** and
**post-condition** respectivey. The meaning of such triples is
the so called *partial correctness* criterion:

     A command (program) c is partially correct w.r.t the specification
     with pre-condition P and post-condition Q if whenever P is true
     before the execution of c and such execution terminates,
     Q is true afterwards

Observe that the termination of the execution of `c` is not ensured by the truth of `P`,
so that when this is not the case the triple `{P}c{Q}` vacuously holds.

A literal formalization of triples and Hoare Logic with Agda would involve the definition of
the language of arithmetic and of its semantics. Following the technique in
chapter 12 of Nipkow and Klein's book, we use a shallow embedding of triples into Agda,
much as we have done for the IMP language until now. Then
pre and post-conditions, **assertions** in Hoare's words, are formalized as Agda
predicates of states:

```
Ass = State → Set

data Triple : Set₁ where
     [_]_[_] : Ass → Com → Ass → Triple
```
*Remark.* In the definition of the data type `Triple` we use square instead of curly braces because
the latter are reserved for implicit arguments in Agda. A further peculiarity of `Triple` is
its type `Set₁` which is the least *universe* such that `Set ≡ Set₀ : Set₁`. This is forced by Agda since
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

```
data ⊢_ : Triple → Set₁ where      -- ⊢ is written \|-

   H-Skip : ∀ {P}
          --------------------
          → ⊢ [ P ] SKIP [ P ]

   H-Loc : ∀ {Q a x}
         → ⊢ [ (λ s → Q (s [ x ::= aval a s ])) ] (x := a) [ Q ]

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
          → ⊢ [ P ] (WHILE b DO c) [ (λ s → P s ∧ bval b s == false) ]

   H-Conseq : ∀ {P Q P′ Q′ : Ass} {c}
          → (∀ s → P′ s → P s)
          → ⊢ [ P  ] c [ Q  ]
          → (∀ s → Q s → Q′ s)
          --------------------
          → ⊢ [ P′ ] c [ Q′ ]


---------------------
-- Soundness Theorem
---------------------

lemma-Hoare-inv : ∀ {P : Ass} {s b c t} →
                  (∀{s' t'} → (P s' ∧ bval b s' == true) → ⦅ c , s' ⦆ ⇒ t' → P t') →
                  P s →
                  ⦅ WHILE b DO c , s ⦆ ⇒ t →
                  P t
                  
lemma-Hoare-inv {P} {s} {b} {c} {.s} hyp1 hyp2 (WhileFalse x) = hyp2
lemma-Hoare-inv {P} {s} {b} {c} {t} hyp1 hyp2
                  (WhileTrue {.c} {.b} {.s} {s'} {s''} x hyp3 hyp4) = claim2 
     where
       claim1 = hyp1 {s} {s'} (hyp2 , x) hyp3               
       claim2 = lemma-Hoare-inv {P} {s'} {b} {c} {t} (hyp1 {_} {_}) claim1 hyp4

lemma-Hoare-loop-exit : ∀ {b c s t}
             → ⦅ WHILE b DO c , s ⦆ ⇒ t → bval b t == false 

lemma-Hoare-loop-exit (WhileFalse x) = x
lemma-Hoare-loop-exit (WhileTrue x hyp1 hyp2) = lemma-Hoare-loop-exit hyp2

lemma-Hoare-sound : ∀ {P c Q s t} →
             ⊢ [ P ] c [ Q ] → 
             P s → 
             ⦅ c , s ⦆ ⇒ t → 
             Q t

lemma-Hoare-sound H-Skip hyp2 Skip = hyp2

lemma-Hoare-sound H-Loc hyp2 Loc = hyp2

lemma-Hoare-sound (H-Comp hyp1 hyp4) hyp2 (Comp hyp3 hyp5) = IH2
      where
         IH1 = lemma-Hoare-sound hyp1 hyp2 hyp3
         IH2 = lemma-Hoare-sound hyp4 IH1 hyp5


lemma-Hoare-sound (H-If hyp1 hyp4) hyp2 (IfTrue x hyp3) = thesis
      where

        IH = lemma-Hoare-sound hyp1
        thesis = IH (hyp2 , x) hyp3

lemma-Hoare-sound (H-If hyp1 hyp4) hyp2 (IfFalse y hyp3) = thesis
      where

        IH = lemma-Hoare-sound hyp4
        thesis = IH (hyp2 , y) hyp3


lemma-Hoare-sound {P} {_} {_} {s} {t}
                  (H-While {_} {b} hyp1) hyp2 hyp3 = Pt , b-false
      where

        Pt : P t
        Pt = lemma-Hoare-inv (lemma-Hoare-sound hyp1 ) hyp2 hyp3 

        b-false : bval b t == false
        b-false = lemma-Hoare-loop-exit hyp3

lemma-Hoare-sound {_} {_} {_} {s} {t} (H-Conseq x hyp1 y) hyp2 hyp3 = ths
      where

        P₁s = x s hyp2
        IH  = lemma-Hoare-sound hyp1
        Q₁s = IH P₁s hyp3
        ths = y t Q₁s

theorem-Hoare-sound : ∀ {P c Q} →
            ⊢ [ P ] c [ Q ] → ⊨ [ P ] c [ Q ]

theorem-Hoare-sound hyp = lemma-Hoare-sound hyp

```
