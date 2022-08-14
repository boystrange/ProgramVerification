---
title: "Big-step operational semantics"
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.BigStep where

open import Bool
open import Nat
open import Nat.Properties
open import Logic
open import Logic.Laws
open import Equality
open import Equality.Reasoning

open import Chapter.AexpBexp

```
-->

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
**big-step operational semantics**
(see [Wikipedia - Operational semantics](https://en.wikipedia.org/wiki/Operational_semantics)
for a short presentation and references), we introduce the relation
`⦅ c , s ⦆⇒ t` whose intended meaning is that the execution of `c` when started in the
state `s` terminates with the final state `t`; in general this requires several steps
that are summrised by a single *big-step*, hence the name.

The definition below uses the trick by Wadler in his PLFA book
(see e.g. the chapter devoted to the [λ-calculus](https://plfa.github.io/Lambda/))
to make the Adga definition of a data type looking as a formal system,
where constructors play the role of rules and the `-------` comments
represent the line separating the premises from the conclusion.


```
data ⦅_,_⦆⇒_ : Com → State → State → Set where 

    Skip : ∀ {s}
         ----------------
         → ⦅ SKIP , s ⦆⇒ s

    Loc : ∀{x a s}
        ---------------------------------------
        → ⦅ x := a , s ⦆⇒ (s [ x ::= aval a s ])

    Comp : ∀{c₁ c₂ s₁ s₂ s₃}
         → ⦅ c₁ , s₁ ⦆⇒ s₂
         → ⦅ c₂ , s₂ ⦆⇒ s₃
           --------------------
         → ⦅ c₁ :: c₂ , s₁ ⦆⇒ s₃
       
    IfTrue : ∀{c₁ c₂ b s t}
           → bval b s == true
           → ⦅ c₁ , s ⦆⇒ t
             -------------------------------
           → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t
         
    IfFalse : ∀{c₁ c₂ b s t}
            → bval b s == false
            → ⦅ c₂ , s ⦆⇒ t
              -------------------------------
            → ⦅ IF b THEN c₁ ELSE c₂ , s ⦆⇒ t    
          
    WhileFalse : ∀{c b s}
               → bval b s == false
                 -----------------------
               → ⦅ WHILE b DO c , s ⦆⇒ s
             
    WhileTrue  : ∀{c b s₁ s₂ s₃}
               → bval b s₁ == true
               → ⦅ c , s₁ ⦆⇒ s₂
               → ⦅ WHILE b DO c , s₂ ⦆⇒ s₃
                 ------------------------
               → ⦅ WHILE b DO c , s₁ ⦆⇒ s₃
```

