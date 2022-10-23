---
title: "Relative Completeness of Hoare Logic"
prev:  Chapter.Imp.HoareLogicSoundness
next:  Chapter.Imp.VerificationConditions
--- 
  
```
module Chapter.Imp.HoareLogicCompleteness where
```

## Imports 

```
open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning

open import Chapter.Imp.AexpBexp
open import Chapter.Imp.BigStep
open import Chapter.Imp.HoareLogic
open import Chapter.Imp.HoareLogicSoundness
```

```
-------------------------
-- Weakest preconditions
-------------------------

wp : Com -> Assn -> Assn
wp c Q s = ∀ t -> ⦅ c , s ⦆ ⇒ t -> Q t

Fact : ∀ {P c Q} -> |= [ P ] c [ Q ] -> (∀ s -> P s -> wp c Q s)
Fact {P} {c} {Q} = only-if
  where
    only-if : ({s t : State} -> P s -> ⦅ c , s ⦆ ⇒ t -> Q t) ->
                            ((s : State) -> P s -> wp c Q s)
    only-if hyp1 s hyp2 t = hyp1 hyp2

-- Execise

    if-part : ((s : State) -> P s -> wp c Q s) ->
                           ({s t : State} -> P s -> ⦅ c , s ⦆ ⇒ t -> Q t)
    if-part hyp1 {s} {t} hyp2 hyp3  = hyp1 s hyp2 t hyp3

---------------
-- Main Lemma
---------------

wp-lemma : ∀ c {Q : Assn} -> |- [ wp c Q ] c [ Q ]

wp-lemma SKIP {Q} = H-Str left-premise H-Skip
  where
    left-premise : ∀ s -> wp SKIP Q s -> Q s
    left-premise s hyp = hyp s Skip

-- hyp : wp SKIP Q s ≡ ∀ t -> ⦅ SKIP , s ⦆ ⇒ t -> Q t
-- hyp s : ⦅ SKIP , s ⦆ ⇒ s -> Q s
-- Skip :  ⦅ SKIP , s ⦆ ⇒ s
-- hyp s Skip : Q s

wp-lemma (x := a) {Q} = H-Str left-premise H-Loc
  where
    left-premise : ∀ s -> wp (x := a) Q s -> Q (s [ x ::= aval a s ])
    left-premise s hyp = hyp (s [ x ::= aval a s ]) Loc

-- hyp : wp (x := a) Q s ≡ ∀ t -> ⦅ x := a , s ⦆ ⇒ t -> Q t
-- hyp (s [ x ::= aval a s ]) : ⦅ x := a , s ⦆ ⇒ (s [ x ::= aval a s ])
--                                             -> Q (s [ x ::= aval a s ])
-- Loc : ⦅ x := a , s ⦆ ⇒ (s [ x ::= aval a s ])
-- hyp (s [ x ::= aval a s ]) Loc : Q (s [ x ::= aval a s ])

wp-lemma (c₁ :: c₂) {Q} = H-Str left-premise (H-Comp IH1 IH2)
  where
    IH1 : |- [ wp c₁ (wp c₂ Q) ] c₁ [ wp c₂ Q ]
    IH1 = wp-lemma c₁ {wp c₂ Q}

    IH2 : |- [ wp c₂ Q ] c₂ [ Q ]
    IH2 = wp-lemma c₂ {Q}

    left-premise : ∀ s -> wp (c₁ :: c₂) Q s -> wp c₁ (wp c₂ Q) s
    left-premise s hyp1 r hyp2 t hyp3 = hyp1 t (Comp hyp2 hyp3)

-- hyp1 : wp (c₁ :: c₂) Q s ≡ ∀ t -> ⦅ c₁ :: c₂ , s ⦆ ⇒ t -> Q t
-- hyp2 : ⦅ c₁ , s ⦆ ⇒ r
-- hyp3 : ⦅ c₂ , r ⦆ ⇒ t
-- Comp hyp2 hyp3 : ⦅ c₁ :: c₂ , s ⦆ ⇒ t

wp-lemma (IF b THEN c₁ ELSE c₂) {Q} = H-If true-premise false-premise
  where
    P = wp (IF b THEN c₁ ELSE c₂) Q

    IH1 : |- [ wp c₁ Q ] c₁ [ Q ]
    IH1 = wp-lemma c₁ {Q}

    left-premise-true : ∀ s -> P s ∧ bval b s == true -> wp c₁ Q s
    left-premise-true s (Ps , b=true) t hyp = Ps t (IfTrue b=true hyp)

-- Ps t : P s t ≡ ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t -> Q t
-- hyp : ⦅ c₁ , s ⦆ ⇒ t
-- b=true : bval b s == true
-- IfTrue b=true hyp : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t

    true-premise : |-  [ (λ s -> P s ∧ bval b s == true) ] c₁ [ Q ]
    true-premise = H-Str left-premise-true IH1

    IH2 : |- [ wp c₂ Q ] c₂ [ Q ]
    IH2 = wp-lemma c₂ {Q}

    left-premise-false : ∀ s -> P s ∧ bval b s == false -> wp c₂ Q s
    left-premise-false s (Ps , b=false) t hyp = Ps t (IfFalse b=false hyp)

-- Ps t : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t -> Q t
-- hyp : ⦅ c₂ , s ⦆ ⇒ t
-- b=false : bval b s == false
-- IfFalse b=false hyp : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t

    false-premise : |- [ (λ s -> P s ∧ bval b s == false) ] c₂ [ Q ]
    false-premise = H-Str left-premise-false IH2

wp-lemma (WHILE b DO c) {Q} = H-Weak claim2 weak-premise
  where
    P = wp (WHILE b DO c) Q

    IH : |- [ wp c P ] c [ P ]
    IH = wp-lemma c {P}

    str-premise : ∀ s -> P s ∧ bval b s == true -> wp c P s
    str-premise s (Ps , b=true) t hyp r w = 
                              Ps r (WhileTrue b=true hyp w)

-- Ps r : ⦅ WHILE b DO c , s ⦆ ⇒ r -> Q r
-- w : ⦅ WHILE b DO c , t ⦆ ⇒ r
-- hyp : ⦅ c , s ⦆ ⇒ t
-- b=true : bval b s == true
-- WhileTrue b=true hyp w : ⦅ WHILE b DO c , s ⦆ ⇒ r
-- Goal: Q r

    claim1 : |- [ (λ s -> P s ∧ bval b s == true) ] c [ P ]
    claim1 = H-Str str-premise IH

    claim2 : |- [ P ] WHILE b DO c [ (λ s -> P s ∧ bval b s == false) ]
    claim2 = H-While claim1

    weak-premise : ∀ s -> P s ∧ bval b s == false -> Q s
    weak-premise s (Ps , b=false) = Ps s (WhileFalse b=false)

-- Ps s : ⦅ WHILE b DO c , s ⦆ ⇒ s -> Q s
-- b=false : bval b s == false
-- WhileFalse b=false : ⦅ WHILE b DO c , s ⦆ ⇒ s

------------------------
-- Completeness Theorem
------------------------

completeness : ∀ (c : Com) {P Q : Assn} -> |= [ P ] c [ Q ] -> |-  [ P ] c [ Q ]
completeness c {P} {Q} hyp = H-Str str-left (wp-lemma c)
  where
    str-left : ∀ s -> P s -> wp c Q s
    str-left = Fact {P} {c} {Q} hyp
```
