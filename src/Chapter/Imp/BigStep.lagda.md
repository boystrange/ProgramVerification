---
title: "Big-step operational semantics"
prev:  Chapter.Imp.AexpBexp
next:  Chapter.Imp.SmallStep 
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}
```
--> 

```
module Chapter.Imp.BigStep where
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

```


In this chapter we introduce the **operational semantics** of IMP, which is a method for
assagning meaning to programs by formally describing their execution. Here we adopt the rather abstract
approach based on the notion of convergence of a program when started in a given state, commonly
called **big-step semantics**.
In the next chapter we shall consider a different approach, based on the definition of a transition system
and called **small-step semantics**:
see [Wikipedia - Operational semantics](https://en.wikipedia.org/wiki/Operational_semantics)
for a short presentation  of both semantics and for references.

## Commands

The syntax of **commands**, namely of instructions and ultimately of IMP programs, is defined by the
grammar

      Com ∋ c, c' ::= SKIP | x := a | c :: c' | IF b THEN c ELSE c' | WHILE b DO c

where `x ∈ Vname`, `a ∈ Aexp` and `b ∈ Bexp`. In the same style of the formalization of
arithmetic and boolean expressions, commands are represented by the following data type `Com`:

```
data Com : Set where
  SKIP  : Com                              -- inaction
  _:=_  : Vname → Aexp → Com              -- assignment
  _::_  : Com → Com → Com                 -- sequence
  IF_THEN_ELSE_ : Bexp → Com → Com → Com  -- conditional
  WHILE_DO_     : Bexp → Com → Com         -- iteration
```

As suggested by the comments in the definition above and by the similarities with
actual programming languages like C and Pascal, commands encode step by step
transformations of the state, that starting with an initial state may reach
a final one in case of termination, or it may run forever.

The command `SKIP` does nothing leaving the state unchanged and roughly corresponds to
the empty block `{}` in C; nonetheless it is usefull to express the one way conditional
`IF b THEN c` written as `IF b THEN c ELSE SKIP` or to represent a terminated program.

The meaning of assignment `x := a`, conditional `IF b THEN c ELSE c'` and iteration
`WHILE b DO c` is as expected; the same holds of sequential composition
`c :: c'` where the unfamiliar symbol :: replaces the semicolon which is not accepted
in operator definitions in Agda.

## The convergence predicate

To reason about IMP programs the informal explanation above has to be transformed into
a formal definition. To this aim and following ideas originally due to Gill Kahn
and widely adopted in the literature under the names of **convergence predicate** and
**big-step operational semantics**, we introduce the relation
`⦅ c , s ⦆ ⇒ t` whose intended meaning is that the execution of `c` when started in the
state `s` terminates with the final state `t`; in general this requires several steps
that are summarised by a single *big-step*, hence the name.

Let us call **configuration** any pair `⦅ c , s ⦆` of a command `c` and a state `s`:
```
data Config : Set where
    ⦅_,_⦆ : Com → State → Config
```
Then we define a binary relation `_⇒_` among `Config` and `State` by 
a formal system that we encode as a data type in Agda following
Wadler's trick in PLFA book
(see e.g. the chapter [Relations](https://plfa.github.io/Relations/))
to make the Adga definition looking as a formal system,
where constructors play the role of rules and in each of them the comment
`-------` represents the line separating the premises from the conclusion.


```
data _⇒_ : Config → State → Set  where

    Skip : ∀ {s}
         ----------------
         → ⦅ SKIP , s ⦆ ⇒ s

    Loc : ∀{x a s}
        ---------------------------------------
        → ⦅ x := a , s ⦆ ⇒ (s [ x ::= aval a s ])

    Comp : ∀{c₁ c₂ s₁ s₂ s₃}
         → ⦅ c₁ , s₁ ⦆ ⇒ s₂
         → ⦅ c₂ , s₂ ⦆ ⇒ s₃
           --------------------
         → ⦅ c₁ :: c₂ , s₁ ⦆ ⇒ s₃
       
    IfTrue : ∀{c₁ c₂ b s t}
           → bval b s == true
           → ⦅ c₁ , s ⦆ ⇒ t
             -------------------------------
           → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t
         
    IfFalse : ∀{c₁ c₂ b s t}
            → bval b s == false
            → ⦅ c₂ , s ⦆ ⇒ t
              -------------------------------
            → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t

    WhileFalse : ∀{c b s}
               → bval b s == false
                 -----------------------
               → ⦅ WHILE b DO c , s ⦆ ⇒ s
             
    WhileTrue  : ∀{c b s₁ s₂ s₃}
               → bval b s₁ == true
               → ⦅ c , s₁ ⦆ ⇒ s₂
               → ⦅ WHILE b DO c , s₂ ⦆ ⇒ s₃
                 ------------------------
               → ⦅ WHILE b DO c , s₁ ⦆ ⇒ s₃

infix 10 _⇒_
```

## Properties

First we show that the convergence predicate is non trivial, namely that
there exist commands that do not produce any final state as the result of their execution;
the simplest ones are of the shape `WHILE B true DO c `, for any `c ∈ Com`.

```
lemma-while-true : ∀ {c : Com} {s t : State} →
               ¬ (⦅ WHILE B true DO c , s ⦆ ⇒ t)

lemma-while-true (WhileTrue x hyp1 hyp2) = lemma-while-true hyp2
```

The proof of this lemma is by contradiction, showing that if there were a proof of
`⦅ WHILE B true DO c , s ⦆ ⇒ t` then an absurdity would follow.
It depends on the hypotheses

        hyp1 : ⦅ c , s ⦆ ⇒ s₂
        hyp2 : ⦅ WHILE B true DO c , s₂ ⦆ ⇒ t

where `s₂ : State` is automatically generated by Agda. In particular
`hyp2` is the hypothetical derivation of a statement that has exactly the same
shape of the absurd hypothesis; nonetheless the induction hypothesis

       lemma-while-true hyp2 : ⊥

is perfectly legal and accepted by Agda. The reason is that the proof is not by
induction over the command `WHILE B true DO c `, rather it is on
the derivation of the absurd hypothesis. As a final remark let us observe that
this is **not** a *reductio ad absurdum*, which is intuitionistically invalid, but
just the proof of a negative statement `¬ A` that is an abbreviation of
the implication `A → ⊥`.

A more relevant property of convergence is that it is **deterministic**: whenever
`⦅ c , s ⦆ ⇒ t` is derivable for some `⦅ c , s ⦆ ∈ Config` and `t ∈ State` the `t` is unique.
Before proving the theorem we need two lemmas.

```
true-neq-false : ¬ (true == false)
true-neq-false = λ ()

lemma-true-neq-false : ∀ {A : Set} → true == false → A
lemma-true-neq-false x = ex-falso (true-neq-false x)
```

In terms of Agda these are *helper functions* to abbreviate the proof of
the following theorem.

```
theorem-deterministic : ∀ {c : Com} {s t t' : State} →
                          ⦅ c , s ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t' → t == t'
                          
theorem-deterministic Skip Skip = refl
theorem-deterministic Loc Loc = refl
theorem-deterministic (Comp hyp1 hyp3) (Comp hyp2 hyp4)
         rewrite theorem-deterministic hyp1 hyp2 |
                 theorem-deterministic hyp3 hyp4 = refl
theorem-deterministic (IfTrue x hyp1) (IfTrue y hyp2)
         rewrite theorem-deterministic hyp1 hyp2 = refl
theorem-deterministic (IfTrue x hyp1) (IfFalse y hyp2)
                     = lemma-true-neq-false abs
         where
            abs : true == false
            abs = tran (symm x) y
theorem-deterministic (IfFalse x hyp1) (IfTrue y hyp2)
                     = lemma-true-neq-false abs
         where
            abs : true == false
            abs = tran (symm y) x
theorem-deterministic (IfFalse x hyp1) (IfFalse y hyp2)
         rewrite theorem-deterministic hyp1 hyp2 = refl
theorem-deterministic (WhileFalse x) (WhileFalse y) = refl
theorem-deterministic (WhileFalse x) (WhileTrue y hyp2 hyp3)
                     = lemma-true-neq-false abs
         where
            abs : true == false
            abs = tran (symm y) x 
theorem-deterministic (WhileTrue x hyp1 hyp3) (WhileFalse y)
                     = lemma-true-neq-false abs
         where
            abs : true == false
            abs = tran (symm x) y
theorem-deterministic (WhileTrue x hyp1 hyp3) (WhileTrue y hyp2 hyp4)
         rewrite theorem-deterministic hyp1 hyp2 |
                 theorem-deterministic hyp3 hyp4 = refl
```

In spite of its intimidating aspect, this proof is a simple symultaneous induction over
the derivations of the hypotheses `⦅ c , s ⦆ ⇒ t` and `⦅ c , s ⦆ ⇒ t'`. Whenever an induction
hypothesis is needed we use the tactic `rewrite` possibly sequencing two hypotheses by means
of the stroke `|`.
The most involved parts in the proof are when treating impossible cases. For example when we have

         IfTrue  x hyp1 : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t
         IfFalse y hyp2 : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t'

it must be the case that `x : bval b s == true` and `y : bval b s == false`. But this leads
to the contradiction `abs : true == false` since `b ∈ Bexp` and `s ∈ State` are the same
in both types. Then by means of `true-neq-false` and the use of the logical law `ex-falso`
(from the library file Logic.Law.agda):

         ex-falso : ∀ {A : Set} → ⊥ → A  -- ex falso quodlibet
         ex-falso = λ ()

in the proof of `lemma-true-neq-false` we can vacuously prove the thesis, as it depends
on an absurd hypothesis.

## Equivalence

We say that two commands `c, c' ∈ Com` are **equivalent** if for all `s ∈ State` the
computations of `⦅c , s⦆` and `⦅c' , s⦆` either both diverge (namely do not converge to any
final state) or it is `⦅c , s⦆ ⇒ t` and `⦅c' , s⦆ ⇒ t` for the same `t ∈ State`. Formally

```
_∼_ : Com → Com → Set     -- the symbol ∼ is written \sim

c ∼ c' = ∀{s t} → ( ⦅ c , s  ⦆ ⇒ t → ⦅ c' , s ⦆ ⇒ t ) ∧
                  ( ⦅ c' , s  ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t )

infixl 19 _∼_
```

Command equivalence is useful when optimizing code, by replacing redundant or inefficient
parts by shorter or more efficient ones. In this section we show some examples; the first
one justifies the simplification of `IF B true THEN c ELSE c'` by `c`.

```
lemma-if-true : ∀ (c c' : Com) →
                IF B true THEN c ELSE c' ∼ c
                
lemma-if-true c c' {s} {t} = only-if-part , if-part
      where
         only-if-part :  ⦅ IF B true THEN c ELSE c' , s ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t
         only-if-part (IfTrue x hyp) = hyp

         if-part : ⦅ c , s ⦆ ⇒ t → ⦅ IF B true THEN c ELSE c' , s ⦆ ⇒ t
         if-part hyp = IfTrue refl hyp
```

A slightly more complex example is the proof that whenever the branches
of a conditional are the same, the conditional itself can be removed:

```
lemma-if-c-c : ∀ (b : Bexp) (c : Com) →
               IF b THEN c ELSE c ∼ c

lemma-if-c-c b c {s} {t} = only-if-part , if-part
      where
         only-if-part : ⦅ IF b THEN c ELSE c , s ⦆ ⇒ t → ⦅ c , s ⦆ ⇒ t
         only-if-part (IfTrue  x hyp) = hyp
         only-if-part (IfFalse x hyp) = hyp

         if-part :  ⦅ c , s ⦆ ⇒ t → ⦅ IF b THEN c ELSE c , s ⦆ ⇒ t
         if-part hyp with lemma-bval-tot b s
         ... | inl x = IfTrue x hyp
         ... | inr x = IfFalse x hyp
```
In the proof of the if-part we use the lemma

      lemma-bval-tot : ∀ (b : Bexp) (s : State) →
                       bval b s == true ∨ bval b s == false

from the chapter 
[Arithmetic and boolean expressions]({% link pages/Chapter.Imp.AexpBexp.md %}) 
(see the solution of exercise 2) stating that given any
`s ∈ State` the value of `b ∈ Bexp` is always computable and it is either `true` or
`false`; then we can select the proper rule among `IfTrue` and `IfFalse` to derive
`⦅ IF b THEN c ELSE c , s ⦆ ⇒ t` from `hyp`
Notice that `lemma-bval-tot b s` is a proof of a disjunction, which
explains the alternative cases in the `with` clause.

## Exercises

1. Prove the lemma

         lemma-if-false : ∀ (c c' : Com) → IF B false THEN c ELSE c' ∼ c'
         
2. Prove the lemma

         lemma-while-false-skip : ∀ {c} → WHILE B false DO c ∼ SKIP
         
3. Prove the lemma

         lemma-while-if : ∀ (b : Bexp) (c : Com) →
                (WHILE b DO c) ∼ (IF b THEN (c :: (WHILE b DO c)) ELSE SKIP)

Hint: you might use implicit arguments in the proofs as in the previous lemmas.


```
-- EXERCISE 1

lemma-if-false : ∀ (c c' : Com) →
                IF B false THEN c ELSE c' ∼ c'

lemma-if-false c c' {s} {t} = only-if-part , if-part
      where
         only-if-part : ⦅ IF B false THEN c ELSE c' , s ⦆ ⇒ t → ⦅ c' , s ⦆ ⇒ t
         only-if-part (IfFalse x hyp) = hyp

         if-part : ⦅ c' , s ⦆ ⇒ t → ⦅ IF B false THEN c ELSE c' , s ⦆ ⇒ t
         if-part hyp = IfFalse refl hyp


-- EXERCISE 2

lemma-while-false-skip : ∀ {c} → WHILE B false DO c ∼ SKIP

lemma-while-false-skip {c} {s} {t} = only-if-part , if-part
      where
         only-if-part : ⦅ WHILE B false DO c , s ⦆ ⇒ t → ⦅ SKIP , s ⦆ ⇒ t
         only-if-part (WhileFalse x) = Skip

         if-part : ⦅ SKIP , s ⦆ ⇒ t → ⦅ WHILE B false DO c , s ⦆ ⇒ t 
         if-part Skip = WhileFalse refl

-- EXERCISE 3

lemma-while-if : ∀ (b : Bexp) (c : Com) →
                (WHILE b DO c) ∼ (IF b THEN (c :: (WHILE b DO c)) ELSE SKIP)
                
lemma-while-if b c {s} {t} = only-if-part , if-part
      where
         only-if-part :
                 ⦅ WHILE b DO c , s ⦆ ⇒ t →
                 ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆ ⇒ t

         only-if-part (WhileFalse x) = IfFalse x Skip
         only-if-part (WhileTrue x hyp1 hyp2) = IfTrue x (Comp hyp1 hyp2)

         if-part :
                 ⦅ IF b THEN c :: (WHILE b DO c) ELSE SKIP , s ⦆ ⇒ t →
                 ⦅ WHILE b DO c , s ⦆ ⇒ t
         if-part (IfTrue x (Comp hyp1 hyp2)) = WhileTrue x hyp1 hyp2
         if-part (IfFalse x Skip) = WhileFalse x
```

{:.solution}
