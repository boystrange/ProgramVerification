---
title: "Introduction to IMP and to Hoare Logic"
next:  Chapter.Imp.AexpBexp 
---

<!--
```
module Chapter.Imp.Introduction where
```
--> 

## The language IMP

To study the verification problem in case of imperative programs we use a tiny programming
language called **IMP** or sometimes **While** in the literature (see below for some references).
The language has just one data type `Val = ℕ`, namely the natural numbers, but two sorts
of expressions, that is *arithmetic* and *boolean expressions*.

An IMP program is a *command*, whose syntax is defined by the grammar:

      Com ∋ c, c' ::= SKIP | x := a | c :: c' | IF b THEN c ELSE c' | WHILE b DO c

This syntax is fearly close to actual programming languages like Pascal or C, but for the
command `SKIP`, that simply terminates the exacution without any side effect, and the
notation `c :: c'` for the more familiar `c ; c'`, forced to us by Agda.  

The meaning of an IMP command is some transformation of the memory;
a *memory state*, or just a *state* is simply represented as
a map `s : State = Varname → Val` assigning a value to each variable identifier in `Varname`.
The formal definition of such meanings is given here in terms of their *operational
semantics*, that is based on some sort of symbolic execution of the commands.

We describe the operational semantics of IMP in two ways. The first one is by means of
the relation `⦅ c , s ⦆ ⇒ t`, where `⦅_,_⦆ ⇒ _ ⊆ (Com × State) × State`. Such relation
is called **big-step** operational semantics because it relates the initial to
the final state of a terminating execution of a command:

      ⦅ c , s ⦆ ⇒ t if the execution of c when started in the state s termintes
                    yielding the state t

A second relation we consider is the **small-step** semantics, which is a relation
`⦅ c , s ⦆ ⟶ ⦅ c' , t ⦆`, where `⦅_,_⦆ ⟶ ⦅_,_⦆ ⊆ (Com × State) × (Com × State)`,
whose meaning is

     ⦅ c , s ⦆ ⟶ ⦅ c' , t ⦆ if the execution of the "first" command in c
                    leads from state s to state t, and c' is the part of c
                    that remains to be executed (its "continuation")

where of course we shall make precise, among other things, which part of a command `c` is
its *first* one and which is its *continuation*.

As we shall see, both these relations are *deterministic* that is functional, in the sense that
if `⦅ c , s ⦆ ⇒ t` then such a `t` is unique; similarly, if `⦅ c , s ⦆ ⟶ ⦅ c' , t ⦆`
then `⦅ c' , t ⦆` is uniquely determined by `⦅ c , s ⦆`.

Although different, the two semantics are related by the theorem:

     ∀ c s t . ⦅ c , s ⦆ ⇒ t <==> ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆

where `⟶*` is the least reflexive and transitive relation including `⟶`.

## The Floyd-Hoare logic

The second ingredient for program verification is a language of *specifications*. We adopt
**assertions**, that is formulas of first order arithmetic, enriched with program variables
from IMP. In our formalization an assertion `P : Assn = State → Set` is a predicate
of states; a pair `P, Q` of assertions are *pre-condition* and *post-condition* of a
command `c` in the *triple* `[ P ] c [ Q ]` (written `{P} c {Q}` in the literature,
a notation which is not permitted by Agda, alas) respectively.

A triple `[ P ] c [ Q ]` is *valid*, written `|= [ P ] c [ Q ]`, if

      For any states s and t such that P s and  ⦅ c , s ⦆ ⇒ t it is Q s

in symbols:

      ∀ s t . P s ∧ ⦅ c , s ⦆ ⇒ t ==> Q t

This is known as the *partial correctness criterion*, since the pre-condition `P s` is not
sufficient to imply the termination of the execution of `c` starting with `s`.

Now, the notion of a valid triple is semantic in nature, as it relies on the (operational)
semantics formalized by the big-step relation; worse than this, it is universally quantified
over states, so that proving something about commands solely on the ground of operational
semantics involves more abstract reasoning tools than just considering particular
executions.

What we need is the power of logic, for which we choose Hoare logic.
Hoare logic is a formal system deriving judjments
we shall write as `|- [ P ] c [ Q ]`, whose derivations are finite trees of triples and
predicate implications. Of such a logic
we shall be able to prove that it is *sound*, in the sense that

      |- [ P ] c [ Q ]  ==>  |= [ P ] c [ Q ]          (Soundness Theorem)

Vice versa we shall prove that, provided that all implications among assertions that are
needed in a proof are provable within our system Agda, Hoare logic is also *complete*

      |= [ P ] c [ Q ]  ==>  |- [ P ] c [ Q ]          (Relative Completeness Theorem) 

## Toward automation



