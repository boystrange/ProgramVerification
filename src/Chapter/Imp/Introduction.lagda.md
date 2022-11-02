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

This syntax is close to actual programming languages like Pascal or C, but for the
command `SKIP`, that simply terminates the exacution without any side effect, and the
notation `c :: c'` for the more familiar `c ; c'`, forced to us by Agda.  

The meaning of an IMP command is some transformation of the memory;
a *memory state*, or just a *state*, is simply represented as
a map `s : State` where `State = Varname → Val`, assigning a value to each variable identifier
in `Varname`.
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
                    leads in one step from state s to state t, and c' is the part of c
                    that remains to be executed (its "continuation")

where of course we shall make precise, among other things, which part of a command `c` is
its *first* one and which is its *continuation*.

As we shall see, both these relations are *deterministic* that is they are functional, in the sense that
if `⦅ c , s ⦆ ⇒ t` then such a `t` is unique; similarly, if `⦅ c , s ⦆ ⟶ ⦅ c' , t ⦆`
then `⦅ c' , t ⦆` is uniquely determined by `⦅ c , s ⦆`.

Although different, the two semantics are related as stated in the theorem:

     ∀ c s t . ⦅ c , s ⦆ ⇒ t <==> ⦅ c , s ⦆ ⟶* ⦅ SKIP , t ⦆

where `⟶*` is the least reflexive and transitive relation including `⟶`.

## The Floyd-Hoare logic

The second ingredient for program verification is a language of *specifications*. We adopt
**assertions**, that is formulas of first order arithmetic, enriched with program variables
from IMP. In our formalization an assertion `P : Assn`, where `Assn = State → Set`, is a predicate
of states; a pair `P, Q` of assertions are *pre-condition* and *post-condition* of a
command `c` in the *triple* `[ P ] c [ Q ]` (written `{P} c {Q}` in the literature,
a notation which is not permitted by Agda, alas) respectively.

A triple `[ P ] c [ Q ]` is *valid*, written `|= [ P ] c [ Q ]`, if

      For any states s and t such that P s and  ⦅ c , s ⦆ ⇒ t it is Q s

or in symbols:

      ∀ s t . P s ∧ ⦅ c , s ⦆ ⇒ t ==> Q t

This is known as the *partial correctness criterion*, since the pre-condition `P s` is not
required to imply the termination of the execution of `c` starting with `s`.

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
needed in a proof are provable within our system Agda, Hoare logic is also *complete*:

      |= [ P ] c [ Q ]  ==>  |- [ P ] c [ Q ]          (Relative Completeness Theorem) 

## Toward automation

Using Hoare logic to verify that a program meets its *contract*, namely some pre and post-conditions,
may be awesome. This can be mitigated if we are able to factor out purely logical steps from a proof
based on Hoare logic, since all other steps can be patterned after the syntactical structure of
the program and hence automated.
On the other hand the progress made by automated theorem provers, like the
[SMT solvers](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories),
can be of great help when checking the logical correctness of the **verification conditions** which
are the product of such a factorization.

In the last chapter we shall introduce a variant of IMP such that `WHILE` commands can be decorated
by assertions that are supposed to be their *loop invariants*. Of course it is the responsibility of the
programmer to write the proper invariants; to verify that this is actually the case we will show
that it sufficies to prove that for any state `s` the predicate `vc C Q s`, automatically
computable from the post-condition `Q` and the annotated command `C`, holds to conclude that if
`P` implies the predicate `pre C Q`, that is also computable, then `|- [ P ] strip C [ Q ]` is
derivable, where `strip C` is just the command obtained from the decorated program `C` by deleting all
annotations.

## References and further readings

The language IMP, its semantics and Hoare logic are treated in depth in [1], together with
its denotational semantics, a topic which is not addressed in our text.
The same topics, but considering also
some extensions of the language (there called *While*) is treated in [2], with a chapter dedicated
to some techniques of static analysis.

In spite of its simplicity, the language IMP
is Turing complete; indeed a sublanguage of it is considered in [3] in place of Turing machines
to introduce the basic results of computability theory.
 
The book [4] has been the basis of our work in this last part of the book. It is a concise exposition
of IMP and Hoare logic (with other topics), where all the definitions and results have been checked
using the proof assistant Isabel. The proof assistant and the underlying logic constitutes the main
difference with the present work. While Isabel is based on Higher Order Logic, which is
classical logic at higher types, Agda is an implementation of intuitionistic type theory; moreover
Isabel exclusively uses tacticals to prove theorems, and no proof object is produced. On the
contrary the enphasis of the present work is on (constructive) proofs, that with respect to [4]
have been completely reworked.

1. G. Winskel, *The Formal Semantics of Programming Languages*, The MIT Press
2. H. R. Nielson & F. Nielson,
   [*Semantics with Applications*](http://www.cs.ru.nl/~herman/onderwijs/semantics2019/wiley.pdf), Wiley  
3. A. J. Kfoury, R. N. Moll & R. A. Arbib, *A Programming Approach to Computability*, Springer
4. T. Nipkow & G. Klein,[*Concrete Semantics*](http://concrete-semantics.org/), Springer
