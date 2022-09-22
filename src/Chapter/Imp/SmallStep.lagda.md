---
title: "Small-step operational semantics"
prev:  Chapter.Imp.BigStep
next:  Chapter.Imp.HoareLogic 
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
-->

```
module Chapter.Imp.SmallStep where
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
``` 

An alternative approach to the operational semantics w.r.t. the big-step semantics is 
the **structured operational semantics** initiated by Gordon Plotkin in his famous
*Pisa notes*, and commonly called **small-step** semantics in the literature.
The idea is to describe the computation of a command out of
an initial state via a transition relation modelling its execution step by step. 

## One-step reduction relation 

Recall that a  **configuration** is a pair `⦅ c , s ⦆` of a command `c` and a state `s`.
Then we define the relation `⦅ c , s ⦆ ⟶ ⦅ c' , s' ⦆` to model the execution of the "leftmost"
command in `c` starting with `s` and  producing a new configuration `⦅ c' , s' ⦆` where
`c'` is what remains to be executed of `c`, called the **continuation**, and
`s'` is the new state produced by the execution step. By adopting terminology
from the λ-calculus, when `⦅ c , s ⦆ ⟶ ⦅ c' , s' ⦆` holds
we say that `⦅ c , s ⦆` **reduces in one step** to `⦅ c' , s' ⦆` and call
the relation `⟶` the **one-step reduction**.


```
data _⟶_ : Config -> Config -> Set where  -- the symbol ⟶ is written \-->


  Loc : ∀{x a s}
        --------------------------------------------------
      -> ⦅ x := a , s ⦆ ⟶ ⦅ SKIP , s [ x ::= aval a s ] ⦆

  Comp₁ : ∀{c s}
          ---------------------------------
          -> ⦅ SKIP :: c , s ⦆ ⟶ ⦅ c , s ⦆
        
  Comp₂ : ∀{c₁ c₁′ c₂ s s′}
          -> ⦅ c₁ , s ⦆ ⟶ ⦅ c₁′ , s′ ⦆
          -----------------------------------------
          -> ⦅ c₁ :: c₂ , s ⦆ ⟶ ⦅ c₁′ :: c₂ , s′ ⦆
        
  IfTrue  : ∀{b s c₁ c₂}
          -> bval b s == true
          ---------------------------------------------
          -> ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⟶ ⦅ c₁ , s ⦆
          
  IfFalse : ∀{b s c₁ c₂}
          -> bval b s == false
          ---------------------------------------------
          -> ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⟶ ⦅ c₂ , s ⦆
          
  While : ∀{b c s}
          ----------------------------------------------------------------------------
          -> ⦅ WHILE b DO c , s ⦆ ⟶ ⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s ⦆
```
In the above definition observe that for no `s` there is a configuration such that
`⦅ SKIP , s ⦆` can be reduced to it: we call such configurations **terminated** and
`SKIP` the **terminated command**.

Rules `Comp₁` and `Comp₂` tell that to execute the configuration
`⦅ c₁ :: c₂ , s ⦆` either `c₁` is terminated, namely it is the command `SKIP`,
so that the computation will proceed by `⦅ c₂ , s ⦆`, 
or we have to reduce in one step `⦅ c₁ , s⦆` to some `⦅ c₁′ , s′ ⦆` so obtaining
the new configuration `⦅ c₁′ :: c₂ , s′ ⦆` to proceed in the execution.

Rules `IfTrue` and `IfFalse` are clear. To understand rule `While` one should think
to what happens with ordinary programming languages like C when excuting a
`WHILE b DO c` command, where `b ∈ Bexp` is the *guard* and `c ∈ Com` the *body* of
the iteration.
Indeed the execution begins by checking the value of
`b`; if it is `false` then the execution terminates, which is
represented by the `SKIP` in the fals branch of the continuation;
otherwise the value of `b` is `true` and the execution will proceed by executing `c`
and then by repeating the `WHILE b DO c` command: this exatcly the true branch in the `IF`, namely
`c :: (WHILE b DO c)`. Incidentally we observe that the continuation in the reducion rule `While`
is justified w.r.t. the big-step semantics by the equivalence in `lemma-while-if` from
exercise 3 in chapter [Big-step operational semantics]({% link pages/Chapter.Imp.BigStep.md %}). 


## Reflexive and transitive closure of one-step reduction

In mathematics the reflexive and transitive closure of a binary relation `R`
is the least reflexive and transitive relation `R*` including `R`.
Having defined the one-step reduction `⟶`, we consider its reflexive and transitive
closure `⟶*` to model executions of arbitrary length, and we dub it
**multi-step reduction** or just **reduction**. 

```
data  _⟶*_ : Config -> Config -> Set where

   ⟶*-refl : ∀ {c s} -> ⦅ c , s ⦆ ⟶* ⦅ c , s ⦆  -- reflexivity
   ⟶*-incl : ∀ {c1 s1 c2 s2 c3 s3} ->            -- including ⟶
                 ⦅ c1 , s1 ⦆ ⟶ ⦅ c2 , s2 ⦆ ->
                 ⦅ c2 , s2 ⦆ ⟶* ⦅ c3 , s3 ⦆ ->
                 ⦅ c1 , s1 ⦆ ⟶* ⦅ c3 , s3 ⦆
```

The rule `⟶*-refl` postulates that `⟶*` is reflexive; the rule `⟶*-incl` states that
by putting a one-step reduction `⦅ c1 , s1 ⦆ ⟶ ⦅ c2 , s2 ⦆` in front of the
multi-step reduction `⦅ c2 , s2 ⦆ ⟶* ⦅ c3 , s3 ⦆` one obtains the new reduction
`⦅ c1 , s1 ⦆ ⟶* ⦅ c3 , s3 ⦆`; not surprisingly the definition
of `->*-incl` reminds that of `cons` for lists. The effect of this rule is that
the relation `⟶*` is transitive, as shown below.

```
⟶*-tran : ∀ {c1 s1 c2 s2 c3 s3} ->
                 ⦅ c1 , s1 ⦆ ⟶* ⦅ c2 , s2 ⦆ ->
                 ⦅ c2 , s2 ⦆ ⟶* ⦅ c3 , s3 ⦆ ->
                 ⦅ c1 , s1 ⦆ ⟶* ⦅ c3 , s3 ⦆

⟶*-tran ⟶*-refl hyp2 = hyp2
⟶*-tran (⟶*-incl x hyp1) hyp2 = ⟶*-incl x (⟶*-tran hyp1 hyp2)
```

In the examples and in the proofs it is more handy to use
some Agda functions allowing to concatenate both one-step and
multi-step reductions. They are some sort of *macros*
in the same style of the function `_==⟨_⟩` for equational reasoning:

```
⦅_,_⦆∎ : ∀ c s -> ⦅ c , s ⦆ ⟶* ⦅ c , s ⦆
⦅ c , s ⦆∎ = ⟶*-refl

⦅_,_⦆⟶⟨_⟩_ : ∀ c s {c' c'' s' s''} ->
             ⦅ c , s ⦆ ⟶ ⦅ c' , s' ⦆ ->
             ⦅ c' , s' ⦆ ⟶* ⦅ c'' , s'' ⦆ ->
             ⦅ c , s ⦆ ⟶* ⦅ c'' , s'' ⦆
⦅ c , s ⦆⟶⟨ x ⟩ y = ⟶*-incl x y

⦅_,_⦆⟶*⟨_⟩_ : ∀ c s {c' c'' s' s''} ->
             ⦅ c , s ⦆ ⟶* ⦅ c' , s' ⦆ ->
             ⦅ c' , s' ⦆ ⟶* ⦅ c'' , s'' ⦆ ->
             ⦅ c , s ⦆ ⟶* ⦅ c'' , s'' ⦆

⦅ c , s ⦆⟶*⟨ x ⟩ y = ⟶*-tran x y
```

## Relating big-step and small-step operational semantics

Although conceptually different, both the big-step and the small-step semantics
model the same notion of execution of IMP programs, namely the same interpreter.
This is not to say that
the relations `_⇒_` and `_⟶*_` coincide, as they have different co-domains, that are
the sets of states and of configurations respectively, which is reflected by
their different types in Agda. Instead we can prove the following
**Big and Small-step Equivalence Theorem**:
      
      Given any c ∈ Com and s, t ∈ State

               ⦅ c , s ⦆ ⇒ t if and only if ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆


We proceed by first establishing `theorem-small-big`, namely the if part
of the Equivalence Theorem above. Its proof uses `lemma-small-big` talling that
if a configuration reduces in one step to a second one which converges to a
state, then the former converges to the same state.

```
lemma-small-big : ∀ {c1 s1 c2 s2 t} ->
                 ⦅ c1 , s1 ⦆ ⟶ ⦅ c2 , s2 ⦆ ->
                 ⦅ c2 , s2 ⦆ ⇒ t ->
                 ⦅ c1 , s1 ⦆ ⇒ t

lemma-small-big Loc Skip = Loc
lemma-small-big Comp₁ hyp2 = Comp Skip hyp2
lemma-small-big (Comp₂ hyp1) (Comp hyp2 hyp3) = Comp indHyp hyp3
      where
         indHyp = lemma-small-big hyp1 hyp2
lemma-small-big (IfTrue x) hyp2 = IfTrue x hyp2
lemma-small-big (IfFalse x) hyp2 = IfFalse x hyp2
lemma-small-big While (IfTrue x (Comp hyp2 hyp3)) =
                                           WhileTrue x hyp2 hyp3
lemma-small-big While (IfFalse x Skip) = WhileFalse x
```

Given the lemma, the proof of `theorem-small-big` is a simple induction
over the definition of `⟶*`.
```
theorem-small-big : ∀ {c s t} ->
          ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆ -> ⦅ c , s ⦆ ⇒ t

theorem-small-big ⟶*-refl = Skip
theorem-small-big (⟶*-incl x hyp) = lemma-small-big x indHyp
       where
          indHyp = theorem-small-big hyp
```

Proving the only if part of the Equivalence Theorem is more laborious.
We begin by estblishing `lemma-big-small` which is the extension to `⟶*` of
rule `Comp₂` in the definition of  `⟶`, therefore allowing several setps in the
execution of the `c` command while executing `c :: c''`.
This will be of help in the theorem proof when treating the case of sequential composition.

```
lemma-big-small : ∀ {c c' c'' s s'} ->
                    ⦅ c , s ⦆ ⟶* ⦅ c' , s' ⦆ ->
                    ⦅ c :: c'' , s ⦆ ⟶* ⦅ c' :: c'' , s' ⦆
                    
lemma-big-small ⟶*-refl = ⟶*-refl
lemma-big-small (⟶*-incl x hyp) =
           ⟶*-incl (Comp₂ x) (lemma-big-small hyp)
```

Then we prove `theorem-small-big` by induction over the derivation
of `⦅ c , s ⦆ ⇒ t`. In this proof we profit of the macros for reasoning
about reductions, hopefully making the argument more readable. 
```
theorem-big-small : ∀ {c s t} ->
          ⦅ c , s ⦆ ⇒ t -> ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆

theorem-big-small (Skip {s}) =
           ⦅ SKIP , s ⦆∎
theorem-big-small (Loc {x} {a} {s}) =
           ⦅ x := a , s ⦆⟶⟨ Loc ⟩
           ⦅ SKIP , s [ x ::= aval a s ] ⦆∎
theorem-big-small (Comp {c₁} {c₂} {s₁} {s₂} {s₃} hyp1 hyp2) =
           ⦅ c₁ :: c₂ , s₁ ⦆⟶*⟨ lemma-big-small (theorem-big-small hyp1) ⟩
           ⦅ SKIP :: c₂ , s₂ ⦆⟶⟨ Comp₁ ⟩
           ⦅ c₂ , s₂ ⦆⟶*⟨ theorem-big-small hyp2 ⟩
           ⦅ SKIP , s₃ ⦆∎
theorem-big-small (IfTrue {c₁} {c₂} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⟶⟨ IfTrue x ⟩
           ⦅ c₁ , s ⦆⟶*⟨ theorem-big-small hyp ⟩
           ⦅ SKIP , t ⦆∎
theorem-big-small (IfFalse {c₁} {c₂} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⟶⟨ IfFalse x ⟩
           ⦅ c₂ , s ⦆⟶*⟨ theorem-big-small hyp ⟩
           ⦅ SKIP , t ⦆∎
theorem-big-small (WhileFalse {c} {b} {s} x) =
           ⦅ WHILE b DO c , s ⦆⟶⟨ While ⟩
           ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆⟶⟨ IfFalse x ⟩
           ⦅ SKIP , s ⦆∎
theorem-big-small (WhileTrue {c} {b} {s} {s′} {t} x hyp1 hyp2) =
           ⦅ WHILE b DO c , s ⦆⟶⟨ While ⟩
           ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆⟶⟨ IfTrue x ⟩
           ⦅ c :: (WHILE b DO c) , s ⦆⟶*⟨ lemma-big-small (theorem-big-small hyp1) ⟩
           ⦅ SKIP :: (WHILE b DO c) , s′ ⦆⟶⟨ Comp₁ ⟩
           ⦅ WHILE b DO c , s′ ⦆⟶*⟨ theorem-big-small hyp2 ⟩
           ⦅ SKIP , t ⦆∎
```

We end this chapter observing that the two semantics are equivalent only
with respect to converging executions. Indeed if a configuration
`⦅ c , s ⦆` does not converge then nothing is obtainable from the definition
of `_⇒_`, which tells us only about the postive cases. On the contrary
the reduction relation `_⟶*_` can model even such diverging executions
which correspond to infinite reductions, even if we cannot decide when
this is the case.

As a matter of fact both relations are *semi-decidable*, but not *decidable* in
the sense of computability theory. Semi-decidability follows by the
fact that both relations are defined by finitary formal systems. Their undecidability
is consequence of the fact that both are formal descriptions of an interpreter for IMP
programs. In fact, in spite of its rudimentary syntax, IMP is a Turing complete programming
language, even slightly extending the *While* language used in Kfoury, Mall and Arbib's book
*A Programming Approach to Computability*
as an equivalent substitute for Turing machines. Were either big or small-step relations decidable,
we would have an algorithm deciding the halting problem.

## Exercise

Let `com0` be the command
```
com0 : Com
com0 = (Z := V X) :: ((X := V Y) :: (Y := V Z))
```
swapping the values of `X` and `Y` using `Z` to temporarily save the value of `X`.
Consider the following states:
```
st07 : State
st07 = ((λ z -> 0) [ X ::= 1 ]) [ Y ::= 2 ]

st08 : State
st08 = st07 [ Z ::= aval (V X) st07 ]

st09 : State
st09 = st08 [ X ::= aval (V Y) st08 ]

st10 : State
st10 = st09 [ Y ::= aval (V Z) st09 ]
```
such that
```
_ : st07 X == 1
_ = refl

_ : st07 Y == 2
_ = refl

_ : st10 X == 2
_ = refl

_ : st10 Y == 1
_ = refl
```

By means of the macros for reasoning about reduction, show

      exec0 : ⦅ com0 , st07 ⦆ ⟶* ⦅ SKIP , st10 ⦆




```
exec0 : ⦅ com0 , st07 ⦆ ⟶* ⦅ SKIP , st10 ⦆
exec0 = ⦅ com0 , st07 ⦆⟶⟨ Comp₂ Loc ⟩ 
        ⦅ SKIP :: ((X := V Y) :: (Y := V Z)), st07 [ Z ::= st07 X ] ⦆⟶⟨ Comp₁ ⟩
        ⦅ (X := V Y) :: (Y := V Z) , st08 ⦆⟶⟨ Comp₂ Loc ⟩
        ⦅ SKIP :: (Y := V Z) , st09 ⦆⟶⟨ Comp₁ ⟩ 
        ⦅ Y := V Z , st09 ⦆⟶⟨ Loc ⟩
        ⦅ SKIP , st10 ⦆∎
```
{:.solution}
