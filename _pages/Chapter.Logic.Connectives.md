---
title: Logical connectives and constants
next:  Chapter.Logic.Negation
---

<pre class="Agda"><a id="85" class="Keyword">module</a> <a id="92" href="Chapter.Logic.Connectives.html" class="Module">Chapter.Logic.Connectives</a> <a id="118" class="Keyword">where</a>
</pre>
The logic we have been using so far is based on a limited set of
Agda types:

* **Logical implication** corresponds to the *arrow type*: a proof
  of `A -> B` is a function that, applied to a proof of `A`, yields
  a proof of `B`.
* **Universal quantification** corresponds to the **dependent arrow
  type**: a proof of `∀(x : A) -> B` is a function that, applied to
  an element `x` of type `A`, yields a proof of `B` (where `x` may
  occur in `B`).
* **Equality** `E == F` is the type of proofs showing that `E` is
  equal to `F`. In order to prove equalities we have used
  *reflexivity* and equational reasoning.

In general, we will need a richer set of logical connectives in
order to prove interesting properties of programs. For example, to
prove the correctness of a sorting function on lists we must be able
to state that the list resulting from the function is sorted *and*
that it is also a permutation of the original list. This property is
the *conjunction* of two sub-properties of lists, that is being
sorted and being a permutation of another list. In this chapter we
will see how to represent **conjunction**, **disjunction**,
**truth** and **falsity** in constructive logic by means of suitably
defined data types.

## Imports

<pre class="Agda"><a id="1380" class="Keyword">open</a> <a id="1385" class="Keyword">import</a> <a id="1392" href="Library.Fun.html" class="Module">Library.Fun</a>
<a id="1404" class="Keyword">open</a> <a id="1409" class="Keyword">import</a> <a id="1416" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="1428" class="Keyword">open</a> <a id="1433" class="Keyword">import</a> <a id="1440" href="Library.Bool.html" class="Module">Library.Bool</a>
<a id="1453" class="Keyword">open</a> <a id="1458" class="Keyword">import</a> <a id="1465" href="Library.Equality.html" class="Module">Library.Equality</a>
</pre>
## Conjunction

In constructive logic, a proof of a conjunction `A ∧ B` is a
**pair** `(p , q)` consisting of a proof `p` of `A` and a proof `q`
of `B`. Thus, we can define conjunction as a data type for
representing pairs. Naturally, the data type will be parametric in
the type of the two components of the pair.

<pre class="Agda"><a id="1807" class="Keyword">data</a> <a id="_∧_"></a><a id="1812" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">_∧_</a> <a id="1816" class="Symbol">(</a><a id="1817" href="Chapter.Logic.Connectives.html#1817" class="Bound">A</a> <a id="1819" href="Chapter.Logic.Connectives.html#1819" class="Bound">B</a> <a id="1821" class="Symbol">:</a> <a id="1823" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="1826" class="Symbol">)</a> <a id="1828" class="Symbol">:</a> <a id="1830" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="1834" class="Keyword">where</a>
  <a id="_∧_._,_"></a><a id="1842" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">_,_</a> <a id="1846" class="Symbol">:</a> <a id="1848" href="Chapter.Logic.Connectives.html#1817" class="Bound">A</a> <a id="1850" class="Symbol">-&gt;</a> <a id="1853" href="Chapter.Logic.Connectives.html#1819" class="Bound">B</a> <a id="1855" class="Symbol">-&gt;</a> <a id="1858" href="Chapter.Logic.Connectives.html#1817" class="Bound">A</a> <a id="1860" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="1862" href="Chapter.Logic.Connectives.html#1819" class="Bound">B</a>
</pre>
Notice that we have chosen an infix form for both the data type
`_∧_` and its constructor `_,_`. In this way, we will be able to
write `A ∧ B` for the type of pairs whose first component has type
`A` and whose second component has type `B`. Analogously, we will be
able to write `p , q` for the pair whose first component is `p` and
whose second component is `q`. We specify the fixity of `∧` and `,`
so that they are both right associative.

<pre class="Agda"><a id="2316" class="Keyword">infixr</a> <a id="2323" class="Number">3</a> <a id="2325" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">_∧_</a>
<a id="2329" class="Keyword">infixr</a> <a id="2336" class="Number">4</a> <a id="2338" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">_,_</a>
</pre>
For example, `A ∧ B ∧ C` means `A ∧ (B ∧ C)` and `p , q , r` means
`p , (q , r)`.

The most common way of "consuming" pairs is by performing case
analysis on them. Since the `_∧_` data type has only one
constructor, when we perform case analysis we end up considering
just one case in which the pair has the form `(x , y)`. As an
example, we can define two projections `fst` and `snd` that allow us
to access the two components of a pair.

<pre class="Agda"><a id="fst"></a><a id="2791" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="2795" class="Symbol">:</a> <a id="2797" class="Symbol">∀{</a><a id="2799" href="Chapter.Logic.Connectives.html#2799" class="Bound">A</a> <a id="2801" href="Chapter.Logic.Connectives.html#2801" class="Bound">B</a> <a id="2803" class="Symbol">:</a> <a id="2805" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2808" class="Symbol">}</a> <a id="2810" class="Symbol">-&gt;</a> <a id="2813" href="Chapter.Logic.Connectives.html#2799" class="Bound">A</a> <a id="2815" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="2817" href="Chapter.Logic.Connectives.html#2801" class="Bound">B</a> <a id="2819" class="Symbol">-&gt;</a> <a id="2822" href="Chapter.Logic.Connectives.html#2799" class="Bound">A</a>
<a id="2824" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="2828" class="Symbol">(</a><a id="2829" href="Chapter.Logic.Connectives.html#2829" class="Bound">x</a> <a id="2831" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="2833" class="Symbol">_)</a> <a id="2836" class="Symbol">=</a> <a id="2838" href="Chapter.Logic.Connectives.html#2829" class="Bound">x</a>

<a id="snd"></a><a id="2841" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="2845" class="Symbol">:</a> <a id="2847" class="Symbol">∀{</a><a id="2849" href="Chapter.Logic.Connectives.html#2849" class="Bound">A</a> <a id="2851" href="Chapter.Logic.Connectives.html#2851" class="Bound">B</a> <a id="2853" class="Symbol">:</a> <a id="2855" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2858" class="Symbol">}</a> <a id="2860" class="Symbol">-&gt;</a> <a id="2863" href="Chapter.Logic.Connectives.html#2849" class="Bound">A</a> <a id="2865" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="2867" href="Chapter.Logic.Connectives.html#2851" class="Bound">B</a> <a id="2869" class="Symbol">-&gt;</a> <a id="2872" href="Chapter.Logic.Connectives.html#2851" class="Bound">B</a>
<a id="2874" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="2878" class="Symbol">(_</a> <a id="2881" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="2883" href="Chapter.Logic.Connectives.html#2883" class="Bound">y</a><a id="2884" class="Symbol">)</a> <a id="2886" class="Symbol">=</a> <a id="2888" href="Chapter.Logic.Connectives.html#2883" class="Bound">y</a>
</pre>
Note that `fst` and `snd` are also proofs of two well-known theorems
about conjunctions: if `A ∧ B` is true, then `A` is true (`fst`) and
`B` is true (`snd`).

By combining conjunction (given by the data type `∧`) and
implication (given by the native Agda's arrow type `->`) we can also
model double implication, commonly known as "if and only if".

<pre class="Agda"><a id="_&lt;=&gt;_"></a><a id="3249" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">_&lt;=&gt;_</a> <a id="3255" class="Symbol">:</a> <a id="3257" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3261" class="Symbol">-&gt;</a> <a id="3264" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3268" class="Symbol">-&gt;</a> <a id="3271" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="3275" href="Chapter.Logic.Connectives.html#3275" class="Bound">A</a> <a id="3277" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="3281" href="Chapter.Logic.Connectives.html#3281" class="Bound">B</a> <a id="3283" class="Symbol">=</a> <a id="3285" class="Symbol">(</a><a id="3286" href="Chapter.Logic.Connectives.html#3275" class="Bound">A</a> <a id="3288" class="Symbol">-&gt;</a> <a id="3291" href="Chapter.Logic.Connectives.html#3281" class="Bound">B</a><a id="3292" class="Symbol">)</a> <a id="3294" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="3296" class="Symbol">(</a><a id="3297" href="Chapter.Logic.Connectives.html#3281" class="Bound">B</a> <a id="3299" class="Symbol">-&gt;</a> <a id="3302" href="Chapter.Logic.Connectives.html#3275" class="Bound">A</a><a id="3303" class="Symbol">)</a>
</pre>
<!--
<pre class="Agda"><a id="3319" class="Keyword">infixr</a> <a id="3326" class="Number">1</a> <a id="3328" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">_&lt;=&gt;_</a>
</pre>-->

## Disjunction

In constructive logic, a proof of a disjunction `A ∨ B` is either a
proof of `A` or a proof of `B` together with an indication of which
proof we are providing. This interpretation suggests the
representation of disjunction `∨` as a data type with two
constructors, one taking a proof of `A` and the other taking a proof
of `B`, to yield a proof of `A ∨ B`. The name of the constructor
indicates which of the two proofs is provided. We call the two
constructors `inl` and `inr` for "inject left" and "inject right".

<pre class="Agda"><a id="3879" class="Keyword">data</a> <a id="_∨_"></a><a id="3884" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">_∨_</a> <a id="3888" class="Symbol">(</a><a id="3889" href="Chapter.Logic.Connectives.html#3889" class="Bound">A</a> <a id="3891" href="Chapter.Logic.Connectives.html#3891" class="Bound">B</a> <a id="3893" class="Symbol">:</a> <a id="3895" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3898" class="Symbol">)</a> <a id="3900" class="Symbol">:</a> <a id="3902" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="3906" class="Keyword">where</a>
  <a id="_∨_.inl"></a><a id="3914" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a> <a id="3918" class="Symbol">:</a> <a id="3920" href="Chapter.Logic.Connectives.html#3889" class="Bound">A</a> <a id="3922" class="Symbol">-&gt;</a> <a id="3925" href="Chapter.Logic.Connectives.html#3889" class="Bound">A</a> <a id="3927" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="3929" href="Chapter.Logic.Connectives.html#3891" class="Bound">B</a>
  <a id="_∨_.inr"></a><a id="3933" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="3937" class="Symbol">:</a> <a id="3939" href="Chapter.Logic.Connectives.html#3891" class="Bound">B</a> <a id="3941" class="Symbol">-&gt;</a> <a id="3944" href="Chapter.Logic.Connectives.html#3889" class="Bound">A</a> <a id="3946" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="3948" href="Chapter.Logic.Connectives.html#3891" class="Bound">B</a>
</pre>
We declare `∨` as a right associative operator with smaller
precedence than `∧`.

<pre class="Agda"><a id="4041" class="Keyword">infixr</a> <a id="4048" class="Number">2</a> <a id="4050" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">_∨_</a>
</pre>
As for conjunctions, we will use case analysis on terms of type `A ∨
B`. As an example, we can formulate the elimination principle for
disjunctions as the following function.

<pre class="Agda"><a id="∨-elim"></a><a id="4239" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="4246" class="Symbol">:</a> <a id="4248" class="Symbol">∀{</a><a id="4250" href="Chapter.Logic.Connectives.html#4250" class="Bound">A</a> <a id="4252" href="Chapter.Logic.Connectives.html#4252" class="Bound">B</a> <a id="4254" href="Chapter.Logic.Connectives.html#4254" class="Bound">C</a> <a id="4256" class="Symbol">:</a> <a id="4258" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4261" class="Symbol">}</a> <a id="4263" class="Symbol">-&gt;</a> <a id="4266" class="Symbol">(</a><a id="4267" href="Chapter.Logic.Connectives.html#4250" class="Bound">A</a> <a id="4269" class="Symbol">-&gt;</a> <a id="4272" href="Chapter.Logic.Connectives.html#4254" class="Bound">C</a><a id="4273" class="Symbol">)</a> <a id="4275" class="Symbol">-&gt;</a> <a id="4278" class="Symbol">(</a><a id="4279" href="Chapter.Logic.Connectives.html#4252" class="Bound">B</a> <a id="4281" class="Symbol">-&gt;</a> <a id="4284" href="Chapter.Logic.Connectives.html#4254" class="Bound">C</a><a id="4285" class="Symbol">)</a> <a id="4287" class="Symbol">-&gt;</a> <a id="4290" href="Chapter.Logic.Connectives.html#4250" class="Bound">A</a> <a id="4292" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="4294" href="Chapter.Logic.Connectives.html#4252" class="Bound">B</a> <a id="4296" class="Symbol">-&gt;</a> <a id="4299" href="Chapter.Logic.Connectives.html#4254" class="Bound">C</a>
<a id="4301" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="4308" href="Chapter.Logic.Connectives.html#4308" class="Bound">f</a> <a id="4310" href="Chapter.Logic.Connectives.html#4310" class="Bound">g</a> <a id="4312" class="Symbol">(</a><a id="4313" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a> <a id="4317" href="Chapter.Logic.Connectives.html#4317" class="Bound">x</a><a id="4318" class="Symbol">)</a> <a id="4320" class="Symbol">=</a> <a id="4322" href="Chapter.Logic.Connectives.html#4308" class="Bound">f</a> <a id="4324" href="Chapter.Logic.Connectives.html#4317" class="Bound">x</a>
<a id="4326" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="4333" href="Chapter.Logic.Connectives.html#4333" class="Bound">f</a> <a id="4335" href="Chapter.Logic.Connectives.html#4335" class="Bound">g</a> <a id="4337" class="Symbol">(</a><a id="4338" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="4342" href="Chapter.Logic.Connectives.html#4342" class="Bound">x</a><a id="4343" class="Symbol">)</a> <a id="4345" class="Symbol">=</a> <a id="4347" href="Chapter.Logic.Connectives.html#4335" class="Bound">g</a> <a id="4349" href="Chapter.Logic.Connectives.html#4342" class="Bound">x</a>
</pre>
For instance, we can use `∨-elim` to prove that disjunction is
commutative:

<pre class="Agda"><a id="∨-comm"></a><a id="4437" href="Chapter.Logic.Connectives.html#4437" class="Function">∨-comm</a> <a id="4444" class="Symbol">:</a> <a id="4446" class="Symbol">∀{</a><a id="4448" href="Chapter.Logic.Connectives.html#4448" class="Bound">A</a> <a id="4450" href="Chapter.Logic.Connectives.html#4450" class="Bound">B</a> <a id="4452" class="Symbol">:</a> <a id="4454" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4457" class="Symbol">}</a> <a id="4459" class="Symbol">-&gt;</a> <a id="4462" href="Chapter.Logic.Connectives.html#4448" class="Bound">A</a> <a id="4464" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="4466" href="Chapter.Logic.Connectives.html#4450" class="Bound">B</a> <a id="4468" class="Symbol">-&gt;</a> <a id="4471" href="Chapter.Logic.Connectives.html#4450" class="Bound">B</a> <a id="4473" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="4475" href="Chapter.Logic.Connectives.html#4448" class="Bound">A</a>
<a id="4477" href="Chapter.Logic.Connectives.html#4437" class="Function">∨-comm</a> <a id="4484" class="Symbol">=</a> <a id="4486" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="4493" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="4497" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a>
</pre>
## Truth

The always true proposition `⊤` is represented as a data type with a
single constructor without arguments. That is, truth is a
proposition for which we can provide a proof without any effort.

<pre class="Agda"><a id="4713" class="Keyword">data</a> <a id="⊤"></a><a id="4718" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a> <a id="4720" class="Symbol">:</a> <a id="4722" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4726" class="Keyword">where</a>
  <a id="⊤.&lt;&gt;"></a><a id="4734" href="Chapter.Logic.Connectives.html#4734" class="InductiveConstructor">&lt;&gt;</a> <a id="4737" class="Symbol">:</a> <a id="4739" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a>
</pre>
## Falsity

The always false proposition `⊥` must not be provable. As such, we
can represent it by a data type without constructors.

<pre class="Agda"><a id="4884" class="Keyword">data</a> <a id="⊥"></a><a id="4889" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="4891" class="Symbol">:</a> <a id="4893" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="4897" class="Keyword">where</a>
</pre>
The elimination principle for `⊥` is sometimes called *principle of
explosion* or *ex falso quodlibet*. It states that if it is possible
to prove `⊥`, then it is possible to prove anything. Stating this
principle in Agda requires the use of the **absurd pattern**.

<pre class="Agda"><a id="ex-falso"></a><a id="5178" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a> <a id="5187" class="Symbol">:</a> <a id="5189" class="Symbol">∀{</a><a id="5191" href="Chapter.Logic.Connectives.html#5191" class="Bound">A</a> <a id="5193" class="Symbol">:</a> <a id="5195" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5198" class="Symbol">}</a> <a id="5200" class="Symbol">-&gt;</a> <a id="5203" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="5205" class="Symbol">-&gt;</a> <a id="5208" href="Chapter.Logic.Connectives.html#5191" class="Bound">A</a>
<a id="5210" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a> <a id="5219" class="Symbol">()</a>
</pre>
The pattern `()` in the definition of `ex-falso` matches an
hypothetical value of type `⊥`. Since no constructor is provided for
`⊥` and no such value may exist, the equation *has no right hand
side* (note that there is no equal sign) and we are not obliged to
provide a proof of `A` as required by the codomain of `ex-falso`.

In other programming languages that are capable of defining a data
type analogous to `⊥` it is possible to assign the type `⊥` to
non-terminating expressions. If this were allowed also in Agda, the
whole language would be useless insofar program verification is
concerned, since `ex-falso` would easily allow us to prove *any*
property about *any* program. For this reason, Agda has a
*termination checker* making sure that every definition is
*terminating*. For example, if define `loop` as follows

<!--
<pre class="Agda"><a id="6065" class="Symbol">{-#</a> <a id="6069" class="Keyword">TERMINATING</a> <a id="6081" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="loop"></a><a id="6097" href="Chapter.Logic.Connectives.html#6097" class="Function">loop</a> <a id="6102" class="Symbol">:</a> <a id="6104" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="6106" class="Symbol">-&gt;</a> <a id="6109" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a>
<a id="6111" href="Chapter.Logic.Connectives.html#6097" class="Function">loop</a> <a id="6116" href="Chapter.Logic.Connectives.html#6116" class="Bound">n</a> <a id="6118" class="Symbol">=</a> <a id="6120" href="Chapter.Logic.Connectives.html#6097" class="Function">loop</a> <a id="6125" class="Symbol">(</a><a id="6126" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6131" href="Chapter.Logic.Connectives.html#6116" class="Bound">n</a><a id="6132" class="Symbol">)</a>
</pre>
Agda reports that this definition does not pass the termination
check. Indeed, `loop` is recursively applied to increasingly larger
arguments. An even simpler example of non-terminating definition is
`bottom`, shown below.

<!--
<pre class="Agda"><a id="6372" class="Symbol">{-#</a> <a id="6376" class="Keyword">TERMINATING</a> <a id="6388" class="Symbol">#-}</a>
</pre>-->
<pre class="Agda"><a id="bottom"></a><a id="6404" href="Chapter.Logic.Connectives.html#6404" class="Function">bottom</a> <a id="6411" class="Symbol">:</a> <a id="6413" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a>
<a id="6415" href="Chapter.Logic.Connectives.html#6404" class="Function">bottom</a> <a id="6422" class="Symbol">=</a> <a id="6424" href="Chapter.Logic.Connectives.html#6404" class="Function">bottom</a>
</pre>
All the recursive functions we have defined until now are verified
by Agda to be *terminating* because there is an argument that
becomes *structurally smaller* from an application of the function
to its recursive invocation. Structural recursion applies to a large
family of functions, but some of them
(e.g. [division](Chapter.Fun.Division.html) or [quick
sort](Chapter.Fun.QuickSort.html)) cannot be easily formulated in
this way. We will see a general technique for having these functions
accepted by Agda in later sections.

## Exercises

1. Prove that conjunction is commutative, namely the theorem
   `∧-comm : ∀{A B : Set} -> A ∧ B -> B ∧ A`.
2. Prove that `∧` and `∨` are idempotent, namely the theorems
   `∧-idem : ∀{A : Set} -> A ∧ A <=> A` and `∨-idem : ∀{A : Set} -> A
   ∨ A <=> A`.
3. Prove that `∧` distributes over `∨` on the left, namely the
   theorem `∧∨-dist : ∀{A B C : Set} -> A ∧ (B ∨ C) <=> (A ∧ B) ∨ (A ∧
   C)`.
4. Prove that `⊤` is the unit of conjuction, namely the theorems
   `∧-unit-l : ∀{A : Set} -> ⊤ ∧ A <=> A` and `∧-unit-r : ∀{A : Set}
   -> A ∧ ⊤ <=> A`.
5. Prove that `⊤` absorbs disjunctions, namely the theorems `∨-⊤-l :
   ∀{A : Set} -> ⊤ ∨ A <=> ⊤` and `∨-⊤-r : ∀{A : Set} -> A ∨ ⊤ <=> ⊤`.
6. Prove that `⊥` is the unit of disjunctions, namely the theorems
   `∨-unit-l : ∀{A : Set} -> ⊥ ∨ A <=> A` and `∨-unit-r : ∀{A : Set}
   -> A ∨ ⊥ <=> A`.
7. Prove that `⊥` absorbs conjunctions, namely the theorems `∧-⊥-l :
   ∀{A : Set} -> ⊥ ∧ A <=> ⊥` and `∧-⊥-r : ∀{A : Set} -> A ∧ ⊥ <=> ⊥`.
8. Prove that every boolean value is either `true` or `false`,
   namely the theorem `Bool-∨ : ∀(b : Bool) -> (b == true) ∨ (b ==
   false)`.

<pre class="Agda"><a id="8112" class="Comment">-- EXERCISE 1</a>
<a id="∧-comm"></a><a id="8126" href="Chapter.Logic.Connectives.html#8126" class="Function">∧-comm</a> <a id="8133" class="Symbol">:</a> <a id="8135" class="Symbol">∀{</a><a id="8137" href="Chapter.Logic.Connectives.html#8137" class="Bound">A</a> <a id="8139" href="Chapter.Logic.Connectives.html#8139" class="Bound">B</a> <a id="8141" class="Symbol">:</a> <a id="8143" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8146" class="Symbol">}</a> <a id="8148" class="Symbol">-&gt;</a> <a id="8151" href="Chapter.Logic.Connectives.html#8137" class="Bound">A</a> <a id="8153" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8155" href="Chapter.Logic.Connectives.html#8139" class="Bound">B</a> <a id="8157" class="Symbol">-&gt;</a> <a id="8160" href="Chapter.Logic.Connectives.html#8139" class="Bound">B</a> <a id="8162" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8164" href="Chapter.Logic.Connectives.html#8137" class="Bound">A</a>
<a id="8166" href="Chapter.Logic.Connectives.html#8126" class="Function">∧-comm</a> <a id="8173" class="Symbol">(</a><a id="8174" href="Chapter.Logic.Connectives.html#8174" class="Bound">x</a> <a id="8176" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8178" href="Chapter.Logic.Connectives.html#8178" class="Bound">y</a><a id="8179" class="Symbol">)</a> <a id="8181" class="Symbol">=</a> <a id="8183" href="Chapter.Logic.Connectives.html#8178" class="Bound">y</a> <a id="8185" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8187" href="Chapter.Logic.Connectives.html#8174" class="Bound">x</a>

<a id="8190" class="Comment">-- EXERCISE 2</a>
<a id="∧-idem"></a><a id="8204" href="Chapter.Logic.Connectives.html#8204" class="Function">∧-idem</a> <a id="8211" class="Symbol">:</a> <a id="8213" class="Symbol">∀{</a><a id="8215" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8217" class="Symbol">:</a> <a id="8219" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8222" class="Symbol">}</a> <a id="8224" class="Symbol">-&gt;</a> <a id="8227" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8229" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8231" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a> <a id="8233" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8237" href="Chapter.Logic.Connectives.html#8215" class="Bound">A</a>
<a id="8239" href="Chapter.Logic.Connectives.html#8204" class="Function">∧-idem</a> <a id="8246" class="Symbol">=</a> <a id="8248" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8252" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8254" class="Symbol">λ</a> <a id="8256" href="Chapter.Logic.Connectives.html#8256" class="Bound">x</a> <a id="8258" class="Symbol">-&gt;</a> <a id="8261" class="Symbol">(</a><a id="8262" href="Chapter.Logic.Connectives.html#8256" class="Bound">x</a> <a id="8264" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8266" href="Chapter.Logic.Connectives.html#8256" class="Bound">x</a><a id="8267" class="Symbol">)</a>

<a id="∨-idem"></a><a id="8270" href="Chapter.Logic.Connectives.html#8270" class="Function">∨-idem</a> <a id="8277" class="Symbol">:</a> <a id="8279" class="Symbol">∀{</a><a id="8281" href="Chapter.Logic.Connectives.html#8281" class="Bound">A</a> <a id="8283" class="Symbol">:</a> <a id="8285" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8288" class="Symbol">}</a> <a id="8290" class="Symbol">-&gt;</a> <a id="8293" href="Chapter.Logic.Connectives.html#8281" class="Bound">A</a> <a id="8295" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8297" href="Chapter.Logic.Connectives.html#8281" class="Bound">A</a> <a id="8299" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8303" href="Chapter.Logic.Connectives.html#8281" class="Bound">A</a>
<a id="8305" href="Chapter.Logic.Connectives.html#8270" class="Function">∨-idem</a> <a id="8312" class="Symbol">=</a> <a id="8314" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="8321" href="Library.Fun.html#27" class="Function">id</a> <a id="8324" href="Library.Fun.html#27" class="Function">id</a> <a id="8327" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8329" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a>

<a id="8334" class="Comment">-- EXERCISE 3</a>
<a id="∧∨-dist"></a><a id="8348" href="Chapter.Logic.Connectives.html#8348" class="Function">∧∨-dist</a> <a id="8356" class="Symbol">:</a> <a id="8358" class="Symbol">∀{</a><a id="8360" href="Chapter.Logic.Connectives.html#8360" class="Bound">A</a> <a id="8362" href="Chapter.Logic.Connectives.html#8362" class="Bound">B</a> <a id="8364" href="Chapter.Logic.Connectives.html#8364" class="Bound">C</a> <a id="8366" class="Symbol">:</a> <a id="8368" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8371" class="Symbol">}</a> <a id="8373" class="Symbol">-&gt;</a> <a id="8376" href="Chapter.Logic.Connectives.html#8360" class="Bound">A</a> <a id="8378" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8380" class="Symbol">(</a><a id="8381" href="Chapter.Logic.Connectives.html#8362" class="Bound">B</a> <a id="8383" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8385" href="Chapter.Logic.Connectives.html#8364" class="Bound">C</a><a id="8386" class="Symbol">)</a> <a id="8388" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8392" class="Symbol">(</a><a id="8393" href="Chapter.Logic.Connectives.html#8360" class="Bound">A</a> <a id="8395" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8397" href="Chapter.Logic.Connectives.html#8362" class="Bound">B</a><a id="8398" class="Symbol">)</a> <a id="8400" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8402" class="Symbol">(</a><a id="8403" href="Chapter.Logic.Connectives.html#8360" class="Bound">A</a> <a id="8405" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8407" href="Chapter.Logic.Connectives.html#8364" class="Bound">C</a><a id="8408" class="Symbol">)</a>
<a id="8410" href="Chapter.Logic.Connectives.html#8348" class="Function">∧∨-dist</a> <a id="8418" class="Symbol">=</a>
  <a id="8422" class="Symbol">(λ</a> <a id="8425" href="Chapter.Logic.Connectives.html#8425" class="Bound">p</a> <a id="8427" class="Symbol">-&gt;</a> <a id="8430" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="8437" class="Symbol">(</a><a id="8438" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a> <a id="8442" href="Library.Fun.html#112" class="Function Operator">∘</a> <a id="8444" class="Symbol">(</a><a id="8445" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8449" href="Chapter.Logic.Connectives.html#8425" class="Bound">p</a> <a id="8451" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,_</a><a id="8453" class="Symbol">))</a> <a id="8456" class="Symbol">(</a><a id="8457" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="8461" href="Library.Fun.html#112" class="Function Operator">∘</a> <a id="8463" class="Symbol">(</a><a id="8464" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8468" href="Chapter.Logic.Connectives.html#8425" class="Bound">p</a> <a id="8470" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,_</a><a id="8472" class="Symbol">))</a> <a id="8475" class="Symbol">(</a><a id="8476" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="8480" href="Chapter.Logic.Connectives.html#8425" class="Bound">p</a><a id="8481" class="Symbol">))</a> <a id="8484" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a>
  <a id="8488" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="8495" class="Symbol">(λ</a> <a id="8498" href="Chapter.Logic.Connectives.html#8498" class="Bound">p</a> <a id="8500" class="Symbol">-&gt;</a> <a id="8503" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8507" href="Chapter.Logic.Connectives.html#8498" class="Bound">p</a> <a id="8509" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8511" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a> <a id="8515" class="Symbol">(</a><a id="8516" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="8520" href="Chapter.Logic.Connectives.html#8498" class="Bound">p</a><a id="8521" class="Symbol">))</a> <a id="8524" class="Symbol">(λ</a> <a id="8527" href="Chapter.Logic.Connectives.html#8527" class="Bound">p</a> <a id="8529" class="Symbol">-&gt;</a> <a id="8532" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8536" href="Chapter.Logic.Connectives.html#8527" class="Bound">p</a> <a id="8538" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8540" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="8544" class="Symbol">(</a><a id="8545" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="8549" href="Chapter.Logic.Connectives.html#8527" class="Bound">p</a><a id="8550" class="Symbol">))</a>

<a id="8554" class="Comment">-- EXERCISE 4</a>
<a id="∧-unit-l"></a><a id="8568" href="Chapter.Logic.Connectives.html#8568" class="Function">∧-unit-l</a> <a id="8577" class="Symbol">:</a> <a id="8579" class="Symbol">∀{</a><a id="8581" href="Chapter.Logic.Connectives.html#8581" class="Bound">A</a> <a id="8583" class="Symbol">:</a> <a id="8585" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8588" class="Symbol">}</a> <a id="8590" class="Symbol">-&gt;</a> <a id="8593" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a> <a id="8595" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8597" href="Chapter.Logic.Connectives.html#8581" class="Bound">A</a> <a id="8599" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8603" href="Chapter.Logic.Connectives.html#8581" class="Bound">A</a>
<a id="8605" href="Chapter.Logic.Connectives.html#8568" class="Function">∧-unit-l</a> <a id="8614" class="Symbol">=</a> <a id="8616" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="8620" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8622" class="Symbol">(</a><a id="8623" href="Chapter.Logic.Connectives.html#4734" class="InductiveConstructor">&lt;&gt;</a> <a id="8626" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,_</a><a id="8628" class="Symbol">)</a>

<a id="∧-unit-r"></a><a id="8631" href="Chapter.Logic.Connectives.html#8631" class="Function">∧-unit-r</a> <a id="8640" class="Symbol">:</a> <a id="8642" class="Symbol">∀{</a><a id="8644" href="Chapter.Logic.Connectives.html#8644" class="Bound">A</a> <a id="8646" class="Symbol">:</a> <a id="8648" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8651" class="Symbol">}</a> <a id="8653" class="Symbol">-&gt;</a> <a id="8656" href="Chapter.Logic.Connectives.html#8644" class="Bound">A</a> <a id="8658" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="8660" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a> <a id="8662" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8666" href="Chapter.Logic.Connectives.html#8644" class="Bound">A</a>
<a id="8668" href="Chapter.Logic.Connectives.html#8631" class="Function">∧-unit-r</a> <a id="8677" class="Symbol">=</a> <a id="8679" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="8683" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8685" class="Symbol">(</a><a id="8686" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">_,</a> <a id="8689" href="Chapter.Logic.Connectives.html#4734" class="InductiveConstructor">&lt;&gt;</a><a id="8691" class="Symbol">)</a>

<a id="8694" class="Comment">-- EXERCISE 5</a>
<a id="∨-unit-l"></a><a id="8708" href="Chapter.Logic.Connectives.html#8708" class="Function">∨-unit-l</a> <a id="8717" class="Symbol">:</a> <a id="8719" class="Symbol">∀{</a><a id="8721" href="Chapter.Logic.Connectives.html#8721" class="Bound">A</a> <a id="8723" class="Symbol">:</a> <a id="8725" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8728" class="Symbol">}</a> <a id="8730" class="Symbol">-&gt;</a> <a id="8733" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="8735" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8737" href="Chapter.Logic.Connectives.html#8721" class="Bound">A</a> <a id="8739" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8743" href="Chapter.Logic.Connectives.html#8721" class="Bound">A</a>
<a id="8745" href="Chapter.Logic.Connectives.html#8708" class="Function">∨-unit-l</a> <a id="8754" class="Symbol">=</a> <a id="8756" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="8763" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a> <a id="8772" href="Library.Fun.html#27" class="Function">id</a> <a id="8775" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8777" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a>

<a id="∨-unit-r"></a><a id="8782" href="Chapter.Logic.Connectives.html#8782" class="Function">∨-unit-r</a> <a id="8791" class="Symbol">:</a> <a id="8793" class="Symbol">∀{</a><a id="8795" href="Chapter.Logic.Connectives.html#8795" class="Bound">A</a> <a id="8797" class="Symbol">:</a> <a id="8799" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8802" class="Symbol">}</a> <a id="8804" class="Symbol">-&gt;</a> <a id="8807" href="Chapter.Logic.Connectives.html#8795" class="Bound">A</a> <a id="8809" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8811" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="8813" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8817" href="Chapter.Logic.Connectives.html#8795" class="Bound">A</a>
<a id="8819" href="Chapter.Logic.Connectives.html#8782" class="Function">∨-unit-r</a> <a id="8828" class="Symbol">=</a> <a id="8830" href="Chapter.Logic.Connectives.html#4239" class="Function">∨-elim</a> <a id="8837" href="Library.Fun.html#27" class="Function">id</a> <a id="8840" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a> <a id="8849" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8851" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a>

<a id="8856" class="Comment">-- EXERCISE 6</a>
<a id="∨-⊤-l"></a><a id="8870" href="Chapter.Logic.Connectives.html#8870" class="Function">∨-⊤-l</a> <a id="8876" class="Symbol">:</a> <a id="8878" class="Symbol">∀{</a><a id="8880" href="Chapter.Logic.Connectives.html#8880" class="Bound">A</a> <a id="8882" class="Symbol">:</a> <a id="8884" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8887" class="Symbol">}</a> <a id="8889" class="Symbol">-&gt;</a> <a id="8892" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a> <a id="8894" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8896" href="Chapter.Logic.Connectives.html#8880" class="Bound">A</a> <a id="8898" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8902" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a>
<a id="8904" href="Chapter.Logic.Connectives.html#8870" class="Function">∨-⊤-l</a> <a id="8910" class="Symbol">=</a> <a id="8912" href="Library.Fun.html#62" class="Function">const</a> <a id="8918" href="Chapter.Logic.Connectives.html#4734" class="InductiveConstructor">&lt;&gt;</a> <a id="8921" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8923" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a>

<a id="∨-⊤-r"></a><a id="8928" href="Chapter.Logic.Connectives.html#8928" class="Function">∨-⊤-r</a> <a id="8934" class="Symbol">:</a> <a id="8936" class="Symbol">∀{</a><a id="8938" href="Chapter.Logic.Connectives.html#8938" class="Bound">A</a> <a id="8940" class="Symbol">:</a> <a id="8942" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="8945" class="Symbol">}</a> <a id="8947" class="Symbol">-&gt;</a> <a id="8950" href="Chapter.Logic.Connectives.html#8938" class="Bound">A</a> <a id="8952" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="8954" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a> <a id="8956" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="8960" href="Chapter.Logic.Connectives.html#4718" class="Datatype">⊤</a>
<a id="8962" href="Chapter.Logic.Connectives.html#8928" class="Function">∨-⊤-r</a> <a id="8968" class="Symbol">=</a> <a id="8970" href="Library.Fun.html#62" class="Function">const</a> <a id="8976" href="Chapter.Logic.Connectives.html#4734" class="InductiveConstructor">&lt;&gt;</a> <a id="8979" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="8981" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a>

<a id="8986" class="Comment">-- EXERCISE 7</a>
<a id="∧-⊥-l"></a><a id="9000" href="Chapter.Logic.Connectives.html#9000" class="Function">∧-⊥-l</a> <a id="9006" class="Symbol">:</a> <a id="9008" class="Symbol">∀{</a><a id="9010" href="Chapter.Logic.Connectives.html#9010" class="Bound">A</a> <a id="9012" class="Symbol">:</a> <a id="9014" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9017" class="Symbol">}</a> <a id="9019" class="Symbol">-&gt;</a> <a id="9022" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="9024" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="9026" href="Chapter.Logic.Connectives.html#9010" class="Bound">A</a> <a id="9028" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="9032" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a>
<a id="9034" href="Chapter.Logic.Connectives.html#9000" class="Function">∧-⊥-l</a> <a id="9040" class="Symbol">=</a> <a id="9042" href="Chapter.Logic.Connectives.html#2791" class="Function">fst</a> <a id="9046" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="9048" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a>

<a id="∧-⊥-r"></a><a id="9058" href="Chapter.Logic.Connectives.html#9058" class="Function">∧-⊥-r</a> <a id="9064" class="Symbol">:</a> <a id="9066" class="Symbol">∀{</a><a id="9068" href="Chapter.Logic.Connectives.html#9068" class="Bound">A</a> <a id="9070" class="Symbol">:</a> <a id="9072" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="9075" class="Symbol">}</a> <a id="9077" class="Symbol">-&gt;</a> <a id="9080" href="Chapter.Logic.Connectives.html#9068" class="Bound">A</a> <a id="9082" href="Chapter.Logic.Connectives.html#1812" class="Datatype Operator">∧</a> <a id="9084" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a> <a id="9086" href="Chapter.Logic.Connectives.html#3249" class="Function Operator">&lt;=&gt;</a> <a id="9090" href="Chapter.Logic.Connectives.html#4889" class="Datatype">⊥</a>
<a id="9092" href="Chapter.Logic.Connectives.html#9058" class="Function">∧-⊥-r</a> <a id="9098" class="Symbol">=</a> <a id="9100" href="Chapter.Logic.Connectives.html#2841" class="Function">snd</a> <a id="9104" href="Chapter.Logic.Connectives.html#1842" class="InductiveConstructor Operator">,</a> <a id="9106" href="Chapter.Logic.Connectives.html#5178" class="Function">ex-falso</a>

<a id="9116" class="Comment">-- EXERCISE 8</a>
<a id="Bool-∨"></a><a id="9130" href="Chapter.Logic.Connectives.html#9130" class="Function">Bool-∨</a> <a id="9137" class="Symbol">:</a> <a id="9139" class="Symbol">∀(</a><a id="9141" href="Chapter.Logic.Connectives.html#9141" class="Bound">b</a> <a id="9143" class="Symbol">:</a> <a id="9145" href="Library.Bool.html#33" class="Datatype">Bool</a><a id="9149" class="Symbol">)</a> <a id="9151" class="Symbol">-&gt;</a> <a id="9154" class="Symbol">(</a><a id="9155" href="Chapter.Logic.Connectives.html#9141" class="Bound">b</a> <a id="9157" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="9160" href="Library.Bool.html#52" class="InductiveConstructor">true</a><a id="9164" class="Symbol">)</a> <a id="9166" href="Chapter.Logic.Connectives.html#3884" class="Datatype Operator">∨</a> <a id="9168" class="Symbol">(</a><a id="9169" href="Chapter.Logic.Connectives.html#9141" class="Bound">b</a> <a id="9171" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="9174" href="Library.Bool.html#57" class="InductiveConstructor">false</a><a id="9179" class="Symbol">)</a>
<a id="9181" href="Chapter.Logic.Connectives.html#9130" class="Function">Bool-∨</a> <a id="9188" href="Library.Bool.html#52" class="InductiveConstructor">true</a>  <a id="9194" class="Symbol">=</a> <a id="9196" href="Chapter.Logic.Connectives.html#3914" class="InductiveConstructor">inl</a> <a id="9200" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="9205" href="Chapter.Logic.Connectives.html#9130" class="Function">Bool-∨</a> <a id="9212" href="Library.Bool.html#57" class="InductiveConstructor">false</a> <a id="9218" class="Symbol">=</a> <a id="9220" href="Chapter.Logic.Connectives.html#3933" class="InductiveConstructor">inr</a> <a id="9224" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

</pre>{:.solution}
