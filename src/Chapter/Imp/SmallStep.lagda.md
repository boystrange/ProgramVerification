---
title: "Small-step operational semantics"
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Imp.SmallStep where

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

An alternative approach to the operational semantics w.r.t. the big-step semantics is 
the **structured operational semantics** also called **small-step** semantics.
The idea is to describe the computation of a command out of
an initial state via a transition relation that depends on the
syntax of the command.

## One-step reduction relation 

Let us call **configuration** any pair `⦅ c , s ⦆` of a command `c` and a state `s`.
Then the predicate `⦅ c , s ⦆→⦅ c' , s' ⦆` represents the execution of the "leftmost"
command in `c` w.r.t. `s` producing a new configuration `⦅ c' , s' ⦆` where
`c'` is what remains to be executed of `c`, called the **continuation**, and
`s'` is the new state produced by the execution step. By abusing terminology
from the λ-calculus, if `⦅ c , s ⦆→⦅ c' , s' ⦆` holds then
we shall say that `⦅ c , s ⦆` **reduces in one step** to `⦅ c' , s' ⦆` and call
the relation `→` **one-step reduction**.


```
data ⦅_,_⦆→⦅_,_⦆ : Com → State → Com → State → Set where


  Loc : ∀{x a s}
        ----------------------------------------------
      → ⦅ x := a , s ⦆→⦅ SKIP , s [ x ::= aval a s ] ⦆

  Comp₁ : ∀{c s}
          --------------------------
        → ⦅ SKIP :: c , s ⦆→⦅ c , s ⦆
        
  Comp₂ : ∀{c₁ c₁′ c₂ s s′}
        → ⦅ c₁       , s ⦆→⦅ c₁′       , s′ ⦆
        ------------------------------------
        → ⦅ c₁ :: c₂ , s ⦆→⦅ c₁′ :: c₂ , s′ ⦆
        
  IfTrue  : ∀{b s c₁ c₂}
          → bval b s == true
            --------------------------------------
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₁ , s ⦆
          
  IfFalse : ∀{b s c₁ c₂}
          → bval b s == false
            --------------------------------------
          → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⦅ c₂ , s ⦆
          
  While : ∀{b c s}
        ---------------------------------------------------------------------
      → ⦅ WHILE b DO c , s ⦆→⦅ IF b THEN (c :: (WHILE b DO c)) ELSE SKIP , s ⦆
```
In the above definition observe that for any `s` there is no configuration such that
`⦅ SKIP , s ⦆` can be reduced to: we call such configurations **terminated** and
`SKIP` the **terminated command**.

Rules `Comp₁` and `Comp₂` tell that to compute the configuration
`⦅ c₁ :: c₂ , s ⦆` either `c₁` is terminated, namely the command `SKIP`,
so that the computation will proceed by `⦅ c₂ , s ⦆` 
or we have first to reduce `⦅ c₁ , s⦆` to some `⦅ c₁′ , s′ ⦆` and then
to contnue with `⦅ c₁′ :: c₂ , s′ ⦆`.

Rules `IfTrue` and `IfFalse` are clear. To understand rule `While` one should think
to what happens with ordinary programming languages like C when excuting a
`WHILE b DO c` command. The computation begins by checking the value of
`b ∈ Bexp`; then if it is `false` then the computation terminates, which is
represented by the `SKIP` in the rule; otherwise the value of `b` is `true`
and the computation proceeds by execiting `c` and then by repeating
the `WHILE b DO c` command: this exatcly the firs branch in the `IF`, namely
`c :: (WHILE b DO c)`. Incidentally we observe that the reducion rule `While`
is semantically justified by the equivalence in `lemma-while-if`.


## Reflexive and tranistive closure of one-step reduction

Having defined the one-step reduction, we consider its reflexive and transitive
closure `→*` to model computations of arbitrary length, and we dub it
**multi-step reduction** or just **reduction**

```
data  ⦅_,_⦆→*⦅_,_⦆ : Com → State → Com → State → Set where

   →*-refl : ∀ {c s} → ⦅ c , s ⦆→*⦅ c , s ⦆  -- reflexivity
   →*-incl : ∀ {c1 s1 c2 s2 c3 s3} →         -- including  ⦅_,_⦆→⦅_,_⦆ 
                 ⦅ c1 , s1 ⦆→⦅ c2 , s2 ⦆ →
                 ⦅ c2 , s2 ⦆→*⦅ c3 , s3 ⦆ →
                 ⦅ c1 , s1 ⦆→*⦅ c3 , s3 ⦆
```

The rule `→*-refl` postulates that `→*` is reflexive; the rule `→-*-incl` states that
by putting a one-step reduction `⦅ c1 , s1 ⦆→⦅ c2 , s2 ⦆` in front of the
multi-step reduction `⦅ c2 , s2 ⦆→*⦅ c3 , s3 ⦆` one obtains the new reduction
`⦅ c1 , s1 ⦆→*⦅ c3 , s3 ⦆`; not surprisingly the definition
of `→*-incl` reminds that of `cons` for lists. The effect of this rule is that
the relation `→*` is transitive, as shown below.

```
→*-tran : ∀ {c1 s1 c2 s2 c3 s3} →
                 ⦅ c1 , s1 ⦆→*⦅ c2 , s2 ⦆ →
                 ⦅ c2 , s2 ⦆→*⦅ c3 , s3 ⦆ →
                 ⦅ c1 , s1 ⦆→*⦅ c3 , s3 ⦆

→*-tran →*-refl hyp2 = hyp2
→*-tran (→*-incl x hyp1) hyp2 =
             →*-incl x (→*-tran hyp1 hyp2)
```

In the examples and in the proofs it is more handy to use
some Agda functions allowing to concatenate both one-step and
multi-step reductions in the same style of the function
`_==⟨_⟩` for equational reasoning:

```
⦅_,_⦆∎ : ∀ c s → ⦅ c , s ⦆→*⦅ c , s ⦆
⦅ c , s ⦆∎ = →*-refl

⦅_,_⦆→⟨_⟩_ : ∀ c s {c' c'' s' s''} →
             ⦅ c , s ⦆→⦅ c' , s' ⦆ →
             ⦅ c' , s' ⦆→*⦅ c'' , s'' ⦆ →
             ⦅ c , s ⦆→*⦅ c'' , s'' ⦆
⦅ c , s ⦆→⟨ x ⟩ y = →*-incl x y

⦅_,_⦆→*⟨_⟩_ : ∀ c s {c' c'' s' s''} →
             ⦅ c , s ⦆→*⦅ c' , s' ⦆ →
             ⦅ c' , s' ⦆→*⦅ c'' , s'' ⦆ →
             ⦅ c , s ⦆→*⦅ c'' , s'' ⦆

⦅ c , s ⦆→*⟨ x ⟩ y = →*-tran x y
```

## Relating big-step and small-step operational semantics 

```
-- Small implies big

lemma-small-big : ∀ {c1 s1 c2 s2 t} →
                 ⦅ c1 , s1 ⦆→⦅ c2 , s2 ⦆ →
                 ⦅ c2 , s2 ⦆⇒ t →
                 ⦅ c1 , s1 ⦆⇒ t

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


theorem-small-big : ∀ {c s t} →
          ⦅ c , s ⦆→*⦅ SKIP , t ⦆ → ⦅ c , s ⦆⇒ t

theorem-small-big →*-refl = Skip
theorem-small-big (→*-incl x hyp) = lemma-small-big x indHyp
       where
          indHyp = theorem-small-big hyp


```

```
-- Big implies small

lemma-big-small : ∀ {c c' c'' s s'} →
                    ⦅ c , s ⦆→*⦅ c' , s' ⦆ →
                    ⦅ c :: c'' , s ⦆→*⦅ c' :: c'' , s' ⦆
                    
lemma-big-small →*-refl = →*-refl
lemma-big-small (→*-incl x hyp) =
           →*-incl (Comp₂ x) (lemma-big-small hyp)
   

theorem-big-small : ∀ {c s t} →
          ⦅ c , s ⦆⇒ t → ⦅ c , s ⦆→*⦅ SKIP , t ⦆

theorem-big-small (Skip {s}) =
           ⦅ SKIP , s ⦆∎
theorem-big-small (Loc {x} {a} {s}) =
           ⦅ x := a , s ⦆→⟨ Loc ⟩
           ⦅ SKIP , s [ x ::= aval a s ] ⦆∎
theorem-big-small (Comp {c₁} {c₂} {s₁} {s₂} {s₃} hyp1 hyp2) =
           ⦅ c₁ :: c₂ , s₁ ⦆→*⟨ lemma-big-small (theorem-big-small hyp1) ⟩
           ⦅ SKIP :: c₂ , s₂ ⦆→⟨ Comp₁ ⟩
           ⦅ c₂ , s₂ ⦆→*⟨ theorem-big-small hyp2 ⟩
           ⦅ SKIP , s₃ ⦆∎
theorem-big-small (IfTrue {c₁} {c₂} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⟨ IfTrue x ⟩
           ⦅ c₁ , s ⦆→*⟨ theorem-big-small hyp ⟩
           ⦅ SKIP , t ⦆∎
theorem-big-small (IfFalse {c₁} {c₂} {b} {s} {t} x hyp) =
           ⦅ IF b THEN c₁ ELSE c₂ , s ⦆→⟨ IfFalse x ⟩
           ⦅ c₂ , s ⦆→*⟨ theorem-big-small hyp ⟩
           ⦅ SKIP , t ⦆∎
theorem-big-small (WhileFalse {c} {b} {s} x) =
           ⦅ WHILE b DO c , s ⦆→⟨ While ⟩
           ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆→⟨ IfFalse x ⟩
           ⦅ SKIP , s ⦆∎
theorem-big-small (WhileTrue {c} {b} {s} {s′} {t} x hyp1 hyp2) =
           ⦅ WHILE b DO c , s ⦆→⟨ While ⟩
           ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆→⟨ IfTrue x ⟩
           ⦅ c :: (WHILE b DO c) , s ⦆→*⟨ lemma-big-small (theorem-big-small hyp1) ⟩
           ⦅ SKIP :: (WHILE b DO c) , s′ ⦆→⟨ Comp₁ ⟩
           ⦅ WHILE b DO c , s′ ⦆→*⟨ theorem-big-small hyp2 ⟩
           ⦅ SKIP , t ⦆∎



```
