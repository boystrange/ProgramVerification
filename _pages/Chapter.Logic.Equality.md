---
title: Equality
prev:  Chapter.Logic.Predicates
next:  Chapter.Logic.LessThan
---

<!--
<pre class="Agda"><a id="97" class="Symbol">{-#</a> <a id="101" class="Keyword">OPTIONS</a> <a id="109" class="Pragma">--allow-unsolved-metas</a> <a id="132" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="149" class="Keyword">module</a> <a id="156" href="Chapter.Logic.Equality.html" class="Module">Chapter.Logic.Equality</a> <a id="179" class="Keyword">where</a>
</pre>
We have now all the necessary ingredients to understand how
propositional equality is defined in Agda.

## Imports

<pre class="Agda"><a id="310" class="Keyword">open</a> <a id="315" class="Keyword">import</a> <a id="322" href="Library.Bool.html" class="Module">Library.Bool</a>
<a id="335" class="Keyword">open</a> <a id="340" class="Keyword">import</a> <a id="347" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="359" class="Keyword">open</a> <a id="364" class="Keyword">import</a> <a id="371" href="Library.List.html" class="Module">Library.List</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="Library.Logic.html" class="Module">Library.Logic</a>
</pre>
## Propositional equality

Propositional equality is nothing but an inductive family with an
implicit parameter `A` (the type of the terms being compared), a
parameter `x` (the leftmost term being compared) and an index (the
rightmost term being compared).

<pre class="Agda"><a id="677" class="Keyword">infix</a> <a id="683" class="Number">4</a> <a id="685" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">_==_</a>

<a id="691" class="Keyword">data</a> <a id="_==_"></a><a id="696" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">_==_</a> <a id="701" class="Symbol">{</a><a id="702" href="Chapter.Logic.Equality.html#702" class="Bound">A</a> <a id="704" class="Symbol">:</a> <a id="706" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="709" class="Symbol">}</a> <a id="711" class="Symbol">(</a><a id="712" href="Chapter.Logic.Equality.html#712" class="Bound">x</a> <a id="714" class="Symbol">:</a> <a id="716" href="Chapter.Logic.Equality.html#702" class="Bound">A</a><a id="717" class="Symbol">)</a> <a id="719" class="Symbol">:</a> <a id="721" href="Chapter.Logic.Equality.html#702" class="Bound">A</a> <a id="723" class="Symbol">-&gt;</a> <a id="726" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="730" class="Keyword">where</a>
  <a id="_==_.refl"></a><a id="738" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="743" class="Symbol">:</a> <a id="745" href="Chapter.Logic.Equality.html#712" class="Bound">x</a> <a id="747" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="750" href="Chapter.Logic.Equality.html#712" class="Bound">x</a>
</pre>
As we can see from its definition, there is just one way of proving
an equality `x == y`, namely by using the constructor `refl`, which
imposes the two compared terms to be the same `x`. The name of this
constructor is intended to suggest that we are using the
*reflexivity* property of equality: every term is equal to
itself. In general, since Agda considers two terms to be "the same"
if they have the same normal form, we can use `refl` to construct
equality proofs for any two terms `x` and `y` that have the same
normal form. We have already seen a few examples of this when
proving [properties of boolean values](Chapter.Intro.BoolProperties.html) and when introducing
[natural numbers](Chapter.Intro.NaturalNumbers.html).

<pre class="Agda"><a id="1492" href="Chapter.Logic.Equality.html#1492" class="Function">_</a> <a id="1494" class="Symbol">:</a> <a id="1496" href="Library.Bool.html#176" class="Function">not</a> <a id="1500" href="Library.Bool.html#52" class="InductiveConstructor">true</a> <a id="1505" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="1508" href="Library.Bool.html#57" class="InductiveConstructor">false</a>
<a id="1514" class="Symbol">_</a> <a id="1516" class="Symbol">=</a> <a id="1518" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>

<a id="1524" href="Chapter.Logic.Equality.html#1524" class="Function">_</a> <a id="1526" class="Symbol">:</a> <a id="1528" class="Number">1</a> <a id="1530" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="1532" class="Number">2</a> <a id="1534" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="1537" class="Number">3</a>
<a id="1539" class="Symbol">_</a> <a id="1541" class="Symbol">=</a> <a id="1543" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>
</pre>
## Symmetry and transitivity

At first, it may be surprising that there are no ways of proving the
equality of two terms `x` and `y` other than reflexivity. After all,
we expect equality to be an equivalence relation, hence it should
also be *symmetric* and *transitive*. As it turns out, symmetry and
transitivity of equality can be proved as consequences of
reflexivity. Their proofs makes use of **dot patterns**, a feature
of Agda that we haven't seen so far.

Let us start with symmetry. The property that we want to prove is
stated as follows.

<pre class="Agda"><a id="symm"></a><a id="2108" href="Chapter.Logic.Equality.html#2108" class="Function">symm</a> <a id="2113" class="Symbol">:</a> <a id="2115" class="Symbol">∀{</a><a id="2117" href="Chapter.Logic.Equality.html#2117" class="Bound">A</a> <a id="2119" class="Symbol">:</a> <a id="2121" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2124" class="Symbol">}</a> <a id="2126" class="Symbol">{</a><a id="2127" href="Chapter.Logic.Equality.html#2127" class="Bound">x</a> <a id="2129" href="Chapter.Logic.Equality.html#2129" class="Bound">y</a> <a id="2131" class="Symbol">:</a> <a id="2133" href="Chapter.Logic.Equality.html#2117" class="Bound">A</a><a id="2134" class="Symbol">}</a> <a id="2136" class="Symbol">-&gt;</a> <a id="2139" href="Chapter.Logic.Equality.html#2127" class="Bound">x</a> <a id="2141" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="2144" href="Chapter.Logic.Equality.html#2129" class="Bound">y</a> <a id="2146" class="Symbol">-&gt;</a> <a id="2149" href="Chapter.Logic.Equality.html#2129" class="Bound">y</a> <a id="2151" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="2154" href="Chapter.Logic.Equality.html#2127" class="Bound">x</a>
<a id="2156" href="Chapter.Logic.Equality.html#2108" class="Function">symm</a> <a id="2161" class="Symbol">{_}</a> <a id="2165" class="Symbol">{</a><a id="2166" href="Chapter.Logic.Equality.html#2166" class="Bound">x</a><a id="2167" class="Symbol">}</a> <a id="2169" class="Symbol">{</a><a id="2170" href="Chapter.Logic.Equality.html#2170" class="Bound">y</a><a id="2171" class="Symbol">}</a> <a id="2173" href="Chapter.Logic.Equality.html#2173" class="Bound">eq</a> <a id="2176" class="Symbol">=</a> <a id="2178" class="Hole">{!!}</a>
</pre>
For the sake of illustration, we have given names to the implicit
arguments `x` and `y`, whereas we have kept `A` unnamed as it plays
no interesting role in the proof. By inspecting the hole, we see
that we have to provide a proof of `y == x` in a context where we
have two elements `x` and `y` of type `A` and a term `eq` of type `x
== y`. Given the current situation, there isn't much we can do
except realize that equality is an inductively defined data type. As
such, we can perform case analysis on `eq`.

<pre class="Agda"><a id="symm₁"></a><a id="2703" href="Chapter.Logic.Equality.html#2703" class="Function">symm₁</a> <a id="2709" class="Symbol">:</a> <a id="2711" class="Symbol">∀{</a><a id="2713" href="Chapter.Logic.Equality.html#2713" class="Bound">A</a> <a id="2715" class="Symbol">:</a> <a id="2717" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="2720" class="Symbol">}</a> <a id="2722" class="Symbol">{</a><a id="2723" href="Chapter.Logic.Equality.html#2723" class="Bound">x</a> <a id="2725" href="Chapter.Logic.Equality.html#2725" class="Bound">y</a> <a id="2727" class="Symbol">:</a> <a id="2729" href="Chapter.Logic.Equality.html#2713" class="Bound">A</a><a id="2730" class="Symbol">}</a> <a id="2732" class="Symbol">-&gt;</a> <a id="2735" href="Chapter.Logic.Equality.html#2723" class="Bound">x</a> <a id="2737" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="2740" href="Chapter.Logic.Equality.html#2725" class="Bound">y</a> <a id="2742" class="Symbol">-&gt;</a> <a id="2745" href="Chapter.Logic.Equality.html#2725" class="Bound">y</a> <a id="2747" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="2750" href="Chapter.Logic.Equality.html#2723" class="Bound">x</a>
<a id="2752" href="Chapter.Logic.Equality.html#2703" class="Function">symm₁</a> <a id="2758" class="Symbol">{_}</a> <a id="2762" class="Symbol">{</a><a id="2763" href="Chapter.Logic.Equality.html#2763" class="Bound">x</a><a id="2764" class="Symbol">}</a> <a id="2766" class="Symbol">{</a><a id="2767" class="DottedPattern Symbol">.</a><a id="2768" href="Chapter.Logic.Equality.html#2763" class="DottedPattern Bound">x</a><a id="2769" class="Symbol">}</a> <a id="2771" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="2776" class="Symbol">=</a> <a id="2778" class="Hole">{!!}</a>
</pre>
As expected, the `eq` argument has turned into `refl`. However, case
analysis has also changed the pattern for the third implicit
argument `y`, which has turned into `.x`. This pattern means that
the third (implicit) argument of `symm` is not arbitrary, but it
must be the same as the second (implicit) argument `x`. The reason
is that the only way the constructor `refl` can be used as evidence
for the equality `x == y` is when `x` and `y` are the same (up to
Agda's definitional equality).

This case analysis has another interesting effect on the context of
the hole that we are supposed to fill. By inspecting the hole we see
that the variable `y` is no longer present, since `x` and `y` have
been *unified*. As a consequence, the type of the hole has changed
from `y == x` to `x == x`. This means that we are now able to
complete the proof, since `refl` will provide evidence of the fact
that `x` is equal to itself.

<pre class="Agda"><a id="symm₂"></a><a id="3716" href="Chapter.Logic.Equality.html#3716" class="Function">symm₂</a> <a id="3722" class="Symbol">:</a> <a id="3724" class="Symbol">∀{</a><a id="3726" href="Chapter.Logic.Equality.html#3726" class="Bound">A</a> <a id="3728" class="Symbol">:</a> <a id="3730" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3733" class="Symbol">}</a> <a id="3735" class="Symbol">{</a><a id="3736" href="Chapter.Logic.Equality.html#3736" class="Bound">x</a> <a id="3738" href="Chapter.Logic.Equality.html#3738" class="Bound">y</a> <a id="3740" class="Symbol">:</a> <a id="3742" href="Chapter.Logic.Equality.html#3726" class="Bound">A</a><a id="3743" class="Symbol">}</a> <a id="3745" class="Symbol">-&gt;</a> <a id="3748" href="Chapter.Logic.Equality.html#3736" class="Bound">x</a> <a id="3750" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="3753" href="Chapter.Logic.Equality.html#3738" class="Bound">y</a> <a id="3755" class="Symbol">-&gt;</a> <a id="3758" href="Chapter.Logic.Equality.html#3738" class="Bound">y</a> <a id="3760" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="3763" href="Chapter.Logic.Equality.html#3736" class="Bound">x</a>
<a id="3765" href="Chapter.Logic.Equality.html#3716" class="Function">symm₂</a> <a id="3771" class="Symbol">{_}</a> <a id="3775" class="Symbol">{</a><a id="3776" href="Chapter.Logic.Equality.html#3776" class="Bound">x</a><a id="3777" class="Symbol">}</a> <a id="3779" class="Symbol">{</a><a id="3780" class="DottedPattern Symbol">.</a><a id="3781" href="Chapter.Logic.Equality.html#3776" class="DottedPattern Bound">x</a><a id="3782" class="Symbol">}</a> <a id="3784" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="3789" class="Symbol">=</a> <a id="3791" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>
</pre>
The proof that equality is transitive follows a similar pattern.

<pre class="Agda"><a id="trans"></a><a id="3871" href="Chapter.Logic.Equality.html#3871" class="Function">trans</a> <a id="3877" class="Symbol">:</a> <a id="3879" class="Symbol">∀{</a><a id="3881" href="Chapter.Logic.Equality.html#3881" class="Bound">A</a> <a id="3883" class="Symbol">:</a> <a id="3885" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3888" class="Symbol">}</a> <a id="3890" class="Symbol">{</a><a id="3891" href="Chapter.Logic.Equality.html#3891" class="Bound">x</a> <a id="3893" href="Chapter.Logic.Equality.html#3893" class="Bound">y</a> <a id="3895" href="Chapter.Logic.Equality.html#3895" class="Bound">z</a> <a id="3897" class="Symbol">:</a> <a id="3899" href="Chapter.Logic.Equality.html#3881" class="Bound">A</a><a id="3900" class="Symbol">}</a> <a id="3902" class="Symbol">-&gt;</a> <a id="3905" href="Chapter.Logic.Equality.html#3891" class="Bound">x</a> <a id="3907" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="3910" href="Chapter.Logic.Equality.html#3893" class="Bound">y</a> <a id="3912" class="Symbol">-&gt;</a> <a id="3915" href="Chapter.Logic.Equality.html#3893" class="Bound">y</a> <a id="3917" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="3920" href="Chapter.Logic.Equality.html#3895" class="Bound">z</a> <a id="3922" class="Symbol">-&gt;</a> <a id="3925" href="Chapter.Logic.Equality.html#3891" class="Bound">x</a> <a id="3927" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="3930" href="Chapter.Logic.Equality.html#3895" class="Bound">z</a>
<a id="3932" href="Chapter.Logic.Equality.html#3871" class="Function">trans</a> <a id="3938" href="Chapter.Logic.Equality.html#3938" class="Bound">eq1</a> <a id="3942" href="Chapter.Logic.Equality.html#3942" class="Bound">eq2</a> <a id="3946" class="Symbol">=</a> <a id="3948" class="Hole">{!!}</a>
</pre>
By performing case analysis on `eq1` and `eq2` we effectively unify
the three (implicit) arguments `x`, `y` and `z`, so that we end up
with having to prove `x == x`, which can be done by reflexivity.

<pre class="Agda"><a id="trans₁"></a><a id="4163" href="Chapter.Logic.Equality.html#4163" class="Function">trans₁</a> <a id="4170" class="Symbol">:</a> <a id="4172" class="Symbol">∀{</a><a id="4174" href="Chapter.Logic.Equality.html#4174" class="Bound">A</a> <a id="4176" class="Symbol">:</a> <a id="4178" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4181" class="Symbol">}</a> <a id="4183" class="Symbol">{</a><a id="4184" href="Chapter.Logic.Equality.html#4184" class="Bound">x</a> <a id="4186" href="Chapter.Logic.Equality.html#4186" class="Bound">y</a> <a id="4188" href="Chapter.Logic.Equality.html#4188" class="Bound">z</a> <a id="4190" class="Symbol">:</a> <a id="4192" href="Chapter.Logic.Equality.html#4174" class="Bound">A</a><a id="4193" class="Symbol">}</a> <a id="4195" class="Symbol">-&gt;</a> <a id="4198" href="Chapter.Logic.Equality.html#4184" class="Bound">x</a> <a id="4200" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4203" href="Chapter.Logic.Equality.html#4186" class="Bound">y</a> <a id="4205" class="Symbol">-&gt;</a> <a id="4208" href="Chapter.Logic.Equality.html#4186" class="Bound">y</a> <a id="4210" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4213" href="Chapter.Logic.Equality.html#4188" class="Bound">z</a> <a id="4215" class="Symbol">-&gt;</a> <a id="4218" href="Chapter.Logic.Equality.html#4184" class="Bound">x</a> <a id="4220" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4223" href="Chapter.Logic.Equality.html#4188" class="Bound">z</a>
<a id="4225" href="Chapter.Logic.Equality.html#4163" class="Function">trans₁</a> <a id="4232" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="4237" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="4242" class="Symbol">=</a> <a id="4244" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>
</pre>
## Congruence and substitution

In the chapter on [natural numbers](Chapter.Intro.NaturalNumbers.html) we have used the congruence
property of function application, namely the property that, if `x ==
y`, then `f x == f y`. We can now see how this theorem is proved.

<pre class="Agda"><a id="cong"></a><a id="4525" href="Chapter.Logic.Equality.html#4525" class="Function">cong</a> <a id="4530" class="Symbol">:</a> <a id="4532" class="Symbol">∀{</a><a id="4534" href="Chapter.Logic.Equality.html#4534" class="Bound">A</a> <a id="4536" href="Chapter.Logic.Equality.html#4536" class="Bound">B</a> <a id="4538" class="Symbol">:</a> <a id="4540" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4543" class="Symbol">}</a> <a id="4545" class="Symbol">(</a><a id="4546" href="Chapter.Logic.Equality.html#4546" class="Bound">f</a> <a id="4548" class="Symbol">:</a> <a id="4550" href="Chapter.Logic.Equality.html#4534" class="Bound">A</a> <a id="4552" class="Symbol">-&gt;</a> <a id="4555" href="Chapter.Logic.Equality.html#4536" class="Bound">B</a><a id="4556" class="Symbol">)</a> <a id="4558" class="Symbol">{</a><a id="4559" href="Chapter.Logic.Equality.html#4559" class="Bound">x</a> <a id="4561" href="Chapter.Logic.Equality.html#4561" class="Bound">y</a> <a id="4563" class="Symbol">:</a> <a id="4565" href="Chapter.Logic.Equality.html#4534" class="Bound">A</a><a id="4566" class="Symbol">}</a> <a id="4568" class="Symbol">-&gt;</a> <a id="4571" href="Chapter.Logic.Equality.html#4559" class="Bound">x</a> <a id="4573" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4576" href="Chapter.Logic.Equality.html#4561" class="Bound">y</a> <a id="4578" class="Symbol">-&gt;</a> <a id="4581" href="Chapter.Logic.Equality.html#4546" class="Bound">f</a> <a id="4583" href="Chapter.Logic.Equality.html#4559" class="Bound">x</a> <a id="4585" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4588" href="Chapter.Logic.Equality.html#4546" class="Bound">f</a> <a id="4590" href="Chapter.Logic.Equality.html#4561" class="Bound">y</a>
<a id="4592" href="Chapter.Logic.Equality.html#4525" class="Function">cong</a> <a id="4597" class="Symbol">_</a> <a id="4599" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="4604" class="Symbol">=</a> <a id="4606" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>
</pre>
Once again we rely on case analysis to force the unification of `x`
and `y`, thereby turning congruence into another case of
reflexivity. Another principle related to equality is
*substitution*, asserting that if `x == y` and we know that `x`
satisfies some predicate `P`, then `y` also satisfies the same
predicate.

<pre class="Agda"><a id="subst"></a><a id="4938" href="Chapter.Logic.Equality.html#4938" class="Function">subst</a> <a id="4944" class="Symbol">:</a> <a id="4946" class="Symbol">∀{</a><a id="4948" href="Chapter.Logic.Equality.html#4948" class="Bound">A</a> <a id="4950" class="Symbol">:</a> <a id="4952" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4955" class="Symbol">}</a> <a id="4957" class="Symbol">(</a><a id="4958" href="Chapter.Logic.Equality.html#4958" class="Bound">P</a> <a id="4960" class="Symbol">:</a> <a id="4962" href="Chapter.Logic.Equality.html#4948" class="Bound">A</a> <a id="4964" class="Symbol">-&gt;</a> <a id="4967" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4970" class="Symbol">)</a> <a id="4972" class="Symbol">{</a><a id="4973" href="Chapter.Logic.Equality.html#4973" class="Bound">x</a> <a id="4975" href="Chapter.Logic.Equality.html#4975" class="Bound">y</a> <a id="4977" class="Symbol">:</a> <a id="4979" href="Chapter.Logic.Equality.html#4948" class="Bound">A</a><a id="4980" class="Symbol">}</a> <a id="4982" class="Symbol">-&gt;</a> <a id="4985" href="Chapter.Logic.Equality.html#4973" class="Bound">x</a> <a id="4987" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="4990" href="Chapter.Logic.Equality.html#4975" class="Bound">y</a> <a id="4992" class="Symbol">-&gt;</a> <a id="4995" href="Chapter.Logic.Equality.html#4958" class="Bound">P</a> <a id="4997" href="Chapter.Logic.Equality.html#4973" class="Bound">x</a> <a id="4999" class="Symbol">-&gt;</a> <a id="5002" href="Chapter.Logic.Equality.html#4958" class="Bound">P</a> <a id="5004" href="Chapter.Logic.Equality.html#4975" class="Bound">y</a>
<a id="5006" href="Chapter.Logic.Equality.html#4938" class="Function">subst</a> <a id="5012" class="Symbol">_</a> <a id="5014" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="5019" href="Chapter.Logic.Equality.html#5019" class="Bound">p</a> <a id="5021" class="Symbol">=</a> <a id="5023" href="Chapter.Logic.Equality.html#5019" class="Bound">p</a>
</pre>
## Equational reasoning

TODO

## Homework

1. Prove that `succ` is injective, namely the theorem
   `succ-injective : ∀{x y : ℕ} -> succ x == succ y -> x == y`.
2. Define the relation `_!=_` as the negation of equality.
   Prove that `zero` is different from any other natural number, namely
   the theorem `zero-succ : ∀{x : ℕ} -> zero != succ x`
3. Prove the theorem `ne-ne : ∀{x y : ℕ} -> succ x != succ y -> x != y`.
4. Prove that `_::_` is injective, namely the theorem
   `::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys ->
   x == y ∧ xs == ys`.
5. Prove a version of `cong` for two-argument functions, namely the
   theorem `cong2 : ∀{A B C : Set} (f : A -> B -> C) {x y : A} {u v :
   B} -> x == y -> u == v -> f x u == f y v`

<pre class="Agda"><a id="5799" class="Comment">-- EXERCISE 1</a>

<a id="succ-injective"></a><a id="5814" href="Chapter.Logic.Equality.html#5814" class="Function">succ-injective</a> <a id="5829" class="Symbol">:</a> <a id="5831" class="Symbol">∀{</a><a id="5833" href="Chapter.Logic.Equality.html#5833" class="Bound">x</a> <a id="5835" href="Chapter.Logic.Equality.html#5835" class="Bound">y</a> <a id="5837" class="Symbol">:</a> <a id="5839" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="5840" class="Symbol">}</a> <a id="5842" class="Symbol">-&gt;</a> <a id="5845" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5850" href="Chapter.Logic.Equality.html#5833" class="Bound">x</a> <a id="5852" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="5855" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5860" href="Chapter.Logic.Equality.html#5835" class="Bound">y</a> <a id="5862" class="Symbol">-&gt;</a> <a id="5865" href="Chapter.Logic.Equality.html#5833" class="Bound">x</a> <a id="5867" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="5870" href="Chapter.Logic.Equality.html#5835" class="Bound">y</a>
<a id="5872" href="Chapter.Logic.Equality.html#5814" class="Function">succ-injective</a> <a id="5887" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="5892" class="Symbol">=</a> <a id="5894" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>

<a id="5900" class="Comment">-- EXERCISE 2</a>

<a id="_!=_"></a><a id="5915" href="Chapter.Logic.Equality.html#5915" class="Function Operator">_!=_</a> <a id="5920" class="Symbol">:</a> <a id="5922" class="Symbol">∀{</a><a id="5924" href="Chapter.Logic.Equality.html#5924" class="Bound">A</a> <a id="5926" class="Symbol">:</a> <a id="5928" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5931" class="Symbol">}</a> <a id="5933" class="Symbol">-&gt;</a> <a id="5936" href="Chapter.Logic.Equality.html#5924" class="Bound">A</a> <a id="5938" class="Symbol">-&gt;</a> <a id="5941" href="Chapter.Logic.Equality.html#5924" class="Bound">A</a> <a id="5943" class="Symbol">-&gt;</a> <a id="5946" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5950" href="Chapter.Logic.Equality.html#5950" class="Bound">x</a> <a id="5952" href="Chapter.Logic.Equality.html#5915" class="Function Operator">!=</a> <a id="5955" href="Chapter.Logic.Equality.html#5955" class="Bound">y</a> <a id="5957" class="Symbol">=</a> <a id="5959" href="Library.Logic.html#1496" class="Function Operator">¬</a> <a id="5961" class="Symbol">(</a><a id="5962" href="Chapter.Logic.Equality.html#5950" class="Bound">x</a> <a id="5964" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="5967" href="Chapter.Logic.Equality.html#5955" class="Bound">y</a><a id="5968" class="Symbol">)</a>

<a id="zero-succ"></a><a id="5971" href="Chapter.Logic.Equality.html#5971" class="Function">zero-succ</a> <a id="5981" class="Symbol">:</a> <a id="5983" class="Symbol">∀{</a><a id="5985" href="Chapter.Logic.Equality.html#5985" class="Bound">x</a> <a id="5987" class="Symbol">:</a> <a id="5989" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="5990" class="Symbol">}</a> <a id="5992" class="Symbol">-&gt;</a> <a id="5995" href="Library.Nat.html#48" class="InductiveConstructor">zero</a> <a id="6000" href="Chapter.Logic.Equality.html#5915" class="Function Operator">!=</a> <a id="6003" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6008" href="Chapter.Logic.Equality.html#5985" class="Bound">x</a>
<a id="6010" href="Chapter.Logic.Equality.html#5971" class="Function">zero-succ</a> <a id="6020" class="Symbol">()</a>

<a id="6024" class="Comment">-- EXERCISE 3</a>

<a id="ne-ne"></a><a id="6039" href="Chapter.Logic.Equality.html#6039" class="Function">ne-ne</a> <a id="6045" class="Symbol">:</a> <a id="6047" class="Symbol">∀{</a><a id="6049" href="Chapter.Logic.Equality.html#6049" class="Bound">x</a> <a id="6051" href="Chapter.Logic.Equality.html#6051" class="Bound">y</a> <a id="6053" class="Symbol">:</a> <a id="6055" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="6056" class="Symbol">}</a> <a id="6058" class="Symbol">-&gt;</a> <a id="6061" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6066" href="Chapter.Logic.Equality.html#6049" class="Bound">x</a> <a id="6068" href="Chapter.Logic.Equality.html#5915" class="Function Operator">!=</a> <a id="6071" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6076" href="Chapter.Logic.Equality.html#6051" class="Bound">y</a> <a id="6078" class="Symbol">-&gt;</a> <a id="6081" href="Chapter.Logic.Equality.html#6049" class="Bound">x</a> <a id="6083" href="Chapter.Logic.Equality.html#5915" class="Function Operator">!=</a> <a id="6086" href="Chapter.Logic.Equality.html#6051" class="Bound">y</a>
<a id="6088" href="Chapter.Logic.Equality.html#6039" class="Function">ne-ne</a> <a id="6094" href="Chapter.Logic.Equality.html#6094" class="Bound">neq</a> <a id="6098" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="6103" class="Symbol">=</a> <a id="6105" href="Chapter.Logic.Equality.html#6094" class="Bound">neq</a> <a id="6109" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>

<a id="6115" class="Comment">-- EXERCISE 4</a>

<a id="::-injective"></a><a id="6130" href="Chapter.Logic.Equality.html#6130" class="Function">::-injective</a> <a id="6143" class="Symbol">:</a> <a id="6145" class="Symbol">∀{</a><a id="6147" href="Chapter.Logic.Equality.html#6147" class="Bound">A</a> <a id="6149" class="Symbol">:</a> <a id="6151" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="6154" class="Symbol">}</a> <a id="6156" class="Symbol">{</a><a id="6157" href="Chapter.Logic.Equality.html#6157" class="Bound">x</a> <a id="6159" href="Chapter.Logic.Equality.html#6159" class="Bound">y</a> <a id="6161" class="Symbol">:</a> <a id="6163" href="Chapter.Logic.Equality.html#6147" class="Bound">A</a><a id="6164" class="Symbol">}</a> <a id="6166" class="Symbol">{</a><a id="6167" href="Chapter.Logic.Equality.html#6167" class="Bound">xs</a> <a id="6170" href="Chapter.Logic.Equality.html#6170" class="Bound">ys</a> <a id="6173" class="Symbol">:</a> <a id="6175" href="Library.List.html#84" class="Datatype">List</a> <a id="6180" href="Chapter.Logic.Equality.html#6147" class="Bound">A</a><a id="6181" class="Symbol">}</a> <a id="6183" class="Symbol">-&gt;</a> <a id="6186" href="Chapter.Logic.Equality.html#6157" class="Bound">x</a> <a id="6188" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="6191" href="Chapter.Logic.Equality.html#6167" class="Bound">xs</a> <a id="6194" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6197" href="Chapter.Logic.Equality.html#6159" class="Bound">y</a> <a id="6199" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="6202" href="Chapter.Logic.Equality.html#6170" class="Bound">ys</a> <a id="6205" class="Symbol">-&gt;</a> <a id="6208" href="Chapter.Logic.Equality.html#6157" class="Bound">x</a> <a id="6210" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6213" href="Chapter.Logic.Equality.html#6159" class="Bound">y</a> <a id="6215" href="Library.Logic.html#1349" class="Function Operator">∧</a> <a id="6217" href="Chapter.Logic.Equality.html#6167" class="Bound">xs</a> <a id="6220" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6223" href="Chapter.Logic.Equality.html#6170" class="Bound">ys</a>
<a id="6226" href="Chapter.Logic.Equality.html#6130" class="Function">::-injective</a> <a id="6239" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="6244" class="Symbol">=</a> <a id="6246" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="6251" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="6253" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>

<a id="6259" class="Comment">-- EXERCISE 5</a>

<a id="cong2"></a><a id="6274" href="Chapter.Logic.Equality.html#6274" class="Function">cong2</a> <a id="6280" class="Symbol">:</a> <a id="6282" class="Symbol">∀{</a><a id="6284" href="Chapter.Logic.Equality.html#6284" class="Bound">A</a> <a id="6286" href="Chapter.Logic.Equality.html#6286" class="Bound">B</a> <a id="6288" href="Chapter.Logic.Equality.html#6288" class="Bound">C</a> <a id="6290" class="Symbol">:</a> <a id="6292" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="6295" class="Symbol">}</a> <a id="6297" class="Symbol">(</a><a id="6298" href="Chapter.Logic.Equality.html#6298" class="Bound">f</a> <a id="6300" class="Symbol">:</a> <a id="6302" href="Chapter.Logic.Equality.html#6284" class="Bound">A</a> <a id="6304" class="Symbol">-&gt;</a> <a id="6307" href="Chapter.Logic.Equality.html#6286" class="Bound">B</a> <a id="6309" class="Symbol">-&gt;</a> <a id="6312" href="Chapter.Logic.Equality.html#6288" class="Bound">C</a><a id="6313" class="Symbol">)</a> <a id="6315" class="Symbol">{</a><a id="6316" href="Chapter.Logic.Equality.html#6316" class="Bound">x</a> <a id="6318" href="Chapter.Logic.Equality.html#6318" class="Bound">y</a> <a id="6320" class="Symbol">:</a> <a id="6322" href="Chapter.Logic.Equality.html#6284" class="Bound">A</a><a id="6323" class="Symbol">}</a> <a id="6325" class="Symbol">{</a><a id="6326" href="Chapter.Logic.Equality.html#6326" class="Bound">u</a> <a id="6328" href="Chapter.Logic.Equality.html#6328" class="Bound">v</a> <a id="6330" class="Symbol">:</a> <a id="6332" href="Chapter.Logic.Equality.html#6286" class="Bound">B</a><a id="6333" class="Symbol">}</a> <a id="6335" class="Symbol">-&gt;</a> <a id="6338" href="Chapter.Logic.Equality.html#6316" class="Bound">x</a> <a id="6340" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6343" href="Chapter.Logic.Equality.html#6318" class="Bound">y</a> <a id="6345" class="Symbol">-&gt;</a> <a id="6348" href="Chapter.Logic.Equality.html#6326" class="Bound">u</a> <a id="6350" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6353" href="Chapter.Logic.Equality.html#6328" class="Bound">v</a> <a id="6355" class="Symbol">-&gt;</a> <a id="6358" href="Chapter.Logic.Equality.html#6298" class="Bound">f</a> <a id="6360" href="Chapter.Logic.Equality.html#6316" class="Bound">x</a> <a id="6362" href="Chapter.Logic.Equality.html#6326" class="Bound">u</a> <a id="6364" href="Chapter.Logic.Equality.html#696" class="Datatype Operator">==</a> <a id="6367" href="Chapter.Logic.Equality.html#6298" class="Bound">f</a> <a id="6369" href="Chapter.Logic.Equality.html#6318" class="Bound">y</a> <a id="6371" href="Chapter.Logic.Equality.html#6328" class="Bound">v</a>
<a id="6373" href="Chapter.Logic.Equality.html#6274" class="Function">cong2</a> <a id="6379" class="Symbol">_</a> <a id="6381" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="6386" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a> <a id="6391" class="Symbol">=</a> <a id="6393" href="Chapter.Logic.Equality.html#738" class="InductiveConstructor">refl</a>
</pre>{:.solution}
