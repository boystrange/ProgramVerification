---
title: Inequality
prev:  Chapter.Logic.Equality
---

<pre class="Agda"><a id="62" class="Keyword">module</a> <a id="69" href="Chapter.Logic.LessThan.html" class="Module">Chapter.Logic.LessThan</a> <a id="92" class="Keyword">where</a>
</pre>
In this section we define the non-strict inequality relation on
natural numbers and prove some of its fundamental properties.

## Imports

<pre class="Agda"><a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="Library.Fun.html" class="Module">Library.Fun</a>
<a id="270" class="Keyword">open</a> <a id="275" class="Keyword">import</a> <a id="282" href="Library.Bool.html" class="Module">Library.Bool</a>
<a id="295" class="Keyword">open</a> <a id="300" class="Keyword">import</a> <a id="307" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="319" class="Keyword">open</a> <a id="324" class="Keyword">import</a> <a id="331" href="Library.Logic.html" class="Module">Library.Logic</a>
<a id="345" class="Keyword">open</a> <a id="350" class="Keyword">import</a> <a id="357" href="Library.Logic.Laws.html" class="Module">Library.Logic.Laws</a>
<a id="376" class="Keyword">open</a> <a id="381" class="Keyword">import</a> <a id="388" href="Library.Equality.html" class="Module">Library.Equality</a>
</pre>
## Non-strict inequality

We define non-strict inequality as an inductive family according to
the following rules.

                                      x <= y
    [le-zero] ------    [le-succ] --------------
              0 <= x              1 + x <= 1 + y

As we will see in a [later section](Chapter.Fun.Division.html), this
is not the only conceivable inference system that defines non-strict
inequality. However, it turns out to be a convenient one in most
situations.

<pre class="Agda"><a id="890" class="Keyword">infix</a> <a id="896" class="Number">4</a> <a id="898" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">_&lt;=_</a>

<a id="904" class="Keyword">data</a> <a id="_&lt;=_"></a><a id="909" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">_&lt;=_</a> <a id="914" class="Symbol">:</a> <a id="916" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="918" class="Symbol">-&gt;</a> <a id="921" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="923" class="Symbol">-&gt;</a> <a id="926" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="930" class="Keyword">where</a>
  <a id="_&lt;=_.le-zero"></a><a id="938" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a> <a id="946" class="Symbol">:</a> <a id="948" class="Symbol">∀{</a><a id="950" href="Chapter.Logic.LessThan.html#950" class="Bound">x</a> <a id="952" class="Symbol">:</a> <a id="954" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="955" class="Symbol">}</a> <a id="957" class="Symbol">-&gt;</a> <a id="960" class="Number">0</a> <a id="962" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="965" href="Chapter.Logic.LessThan.html#950" class="Bound">x</a>
  <a id="_&lt;=_.le-succ"></a><a id="969" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="977" class="Symbol">:</a> <a id="979" class="Symbol">∀{</a><a id="981" href="Chapter.Logic.LessThan.html#981" class="Bound">x</a> <a id="983" href="Chapter.Logic.LessThan.html#983" class="Bound">y</a> <a id="985" class="Symbol">:</a> <a id="987" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="988" class="Symbol">}</a> <a id="990" class="Symbol">-&gt;</a> <a id="993" href="Chapter.Logic.LessThan.html#981" class="Bound">x</a> <a id="995" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="998" href="Chapter.Logic.LessThan.html#983" class="Bound">y</a> <a id="1000" class="Symbol">-&gt;</a> <a id="1003" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1008" href="Chapter.Logic.LessThan.html#981" class="Bound">x</a> <a id="1010" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="1013" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1018" href="Chapter.Logic.LessThan.html#983" class="Bound">y</a>
</pre>
The axiom `le-zero` proves that `0` is the least element, whereas
the rule `le-succ` builds a proof of `succ x <= succ y` from a proof
of `x <= y`. As an example, we can derive `2 <= 3` with two
applications of `le-succ` and one application of `le-zero`. In
general, there are as many applications of `le-succ` as the value of
the smaller number.

<pre class="Agda"><a id="1377" href="Chapter.Logic.LessThan.html#1377" class="Function">_</a> <a id="1379" class="Symbol">:</a> <a id="1381" class="Number">2</a> <a id="1383" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="1386" class="Number">3</a>
<a id="1388" class="Symbol">_</a> <a id="1390" class="Symbol">=</a> <a id="1392" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="1400" class="Symbol">(</a><a id="1401" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="1409" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a><a id="1416" class="Symbol">)</a>
</pre>
## Correctness and completeness

Even though the definition of `<=` seems to make sense, one may
wonder whether it actually characterizes the non-strict inequality
on natural numbers. We can see that this is the case by showing that
`<=` is correct and complete with respect to another
characterization of such relation given in terms of addition.

<pre class="Agda"><a id="_&lt;=ₘ_"></a><a id="1776" href="Chapter.Logic.LessThan.html#1776" class="Function Operator">_&lt;=ₘ_</a> <a id="1782" class="Symbol">:</a> <a id="1784" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1786" class="Symbol">-&gt;</a> <a id="1789" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1791" class="Symbol">-&gt;</a> <a id="1794" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="1798" href="Chapter.Logic.LessThan.html#1798" class="Bound">x</a> <a id="1800" href="Chapter.Logic.LessThan.html#1776" class="Function Operator">&lt;=ₘ</a> <a id="1804" href="Chapter.Logic.LessThan.html#1804" class="Bound">y</a> <a id="1806" class="Symbol">=</a> <a id="1808" href="Library.Logic.html#632" class="Function">∃[</a> <a id="1811" href="Chapter.Logic.LessThan.html#1811" class="Bound">z</a> <a id="1813" href="Library.Logic.html#632" class="Function">]</a> <a id="1815" href="Chapter.Logic.LessThan.html#1798" class="Bound">x</a> <a id="1817" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="1819" href="Chapter.Logic.LessThan.html#1811" class="Bound">z</a> <a id="1821" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="1824" href="Chapter.Logic.LessThan.html#1804" class="Bound">y</a>
</pre>
According to this definition, `x` is not larger than `y` if there
exists some natural number `z` such that `x + z == y`. We can prove
that `<=` implies `<=ₘ` as follows.

<pre class="Agda"><a id="le-correct"></a><a id="2006" href="Chapter.Logic.LessThan.html#2006" class="Function">le-correct</a> <a id="2017" class="Symbol">:</a> <a id="2019" class="Symbol">∀{</a><a id="2021" href="Chapter.Logic.LessThan.html#2021" class="Bound">x</a> <a id="2023" href="Chapter.Logic.LessThan.html#2023" class="Bound">y</a> <a id="2025" class="Symbol">:</a> <a id="2027" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="2028" class="Symbol">}</a> <a id="2030" class="Symbol">-&gt;</a> <a id="2033" href="Chapter.Logic.LessThan.html#2021" class="Bound">x</a> <a id="2035" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="2038" href="Chapter.Logic.LessThan.html#2023" class="Bound">y</a> <a id="2040" class="Symbol">-&gt;</a> <a id="2043" href="Chapter.Logic.LessThan.html#2021" class="Bound">x</a> <a id="2045" href="Chapter.Logic.LessThan.html#1776" class="Function Operator">&lt;=ₘ</a> <a id="2049" href="Chapter.Logic.LessThan.html#2023" class="Bound">y</a>
<a id="2051" href="Chapter.Logic.LessThan.html#2006" class="Function">le-correct</a> <a id="2062" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a> <a id="2070" class="Symbol">=</a> <a id="2072" class="Symbol">_</a> <a id="2074" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="2076" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="2081" href="Chapter.Logic.LessThan.html#2006" class="Function">le-correct</a> <a id="2092" class="Symbol">(</a><a id="2093" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="2101" href="Chapter.Logic.LessThan.html#2101" class="Bound">le</a><a id="2103" class="Symbol">)</a> <a id="2105" class="Keyword">with</a> <a id="2110" href="Chapter.Logic.LessThan.html#2006" class="Function">le-correct</a> <a id="2121" href="Chapter.Logic.LessThan.html#2101" class="Bound">le</a>
<a id="2124" class="Symbol">...</a> <a id="2128" class="Symbol">|</a> <a id="2130" href="Chapter.Logic.LessThan.html#2130" class="Bound">z</a> <a id="2132" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="2134" href="Library.Equality.html#125" class="InductiveConstructor">refl</a> <a id="2139" class="Symbol">=</a> <a id="2141" href="Chapter.Logic.LessThan.html#2130" class="Bound">z</a> <a id="2143" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="2145" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>
The idea is that the `z` in the definition of `<=ₘ` coincides with
the `y` found in the application of `le-zero`. We have used the
underscore since `refl` unifies `z` with `y` when `x` is `0`. For
every application of `le-succ` proving `succ x <= succ y` we
recursively find the `z` such that `x + z == y`, which is the same
`z` such that `succ x + z == succ y`. Note that we cannot simplify
this case to

    le-correct (le-succ le) = le-correct le

even though the result of `le-correct le` superficially appears to
be the same result of `le-correct (le-succ le)`, the reason being
that the two `refl`s prove different equalities (`x + z == y` in the
former case and `succ x + z == succ y` in the latter). In fact,
(some of) the implicit arguments supplied to the two occurrences of
`refl` differ.

We can also show that `<=` is complete with respect to `<=ₘ`.

<pre class="Agda"><a id="le-complete"></a><a id="3023" href="Chapter.Logic.LessThan.html#3023" class="Function">le-complete</a> <a id="3035" class="Symbol">:</a> <a id="3037" class="Symbol">∀{</a><a id="3039" href="Chapter.Logic.LessThan.html#3039" class="Bound">x</a> <a id="3041" href="Chapter.Logic.LessThan.html#3041" class="Bound">y</a> <a id="3043" class="Symbol">:</a> <a id="3045" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="3046" class="Symbol">}</a> <a id="3048" class="Symbol">-&gt;</a> <a id="3051" href="Chapter.Logic.LessThan.html#3039" class="Bound">x</a> <a id="3053" href="Chapter.Logic.LessThan.html#1776" class="Function Operator">&lt;=ₘ</a> <a id="3057" href="Chapter.Logic.LessThan.html#3041" class="Bound">y</a> <a id="3059" class="Symbol">-&gt;</a> <a id="3062" href="Chapter.Logic.LessThan.html#3039" class="Bound">x</a> <a id="3064" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="3067" href="Chapter.Logic.LessThan.html#3041" class="Bound">y</a>
<a id="3069" href="Chapter.Logic.LessThan.html#3023" class="Function">le-complete</a> <a id="3081" class="Symbol">(</a><a id="3082" href="Chapter.Logic.LessThan.html#3082" class="Bound">z</a> <a id="3084" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="3086" href="Library.Equality.html#125" class="InductiveConstructor">refl</a><a id="3090" class="Symbol">)</a> <a id="3092" class="Symbol">=</a> <a id="3094" href="Chapter.Logic.LessThan.html#3112" class="Function">lemma</a>
  <a id="3102" class="Keyword">where</a>
    <a id="3112" href="Chapter.Logic.LessThan.html#3112" class="Function">lemma</a> <a id="3118" class="Symbol">:</a> <a id="3120" class="Symbol">∀{</a><a id="3122" href="Chapter.Logic.LessThan.html#3122" class="Bound">x</a> <a id="3124" href="Chapter.Logic.LessThan.html#3124" class="Bound">y</a> <a id="3126" class="Symbol">:</a> <a id="3128" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="3129" class="Symbol">}</a> <a id="3131" class="Symbol">-&gt;</a> <a id="3134" href="Chapter.Logic.LessThan.html#3122" class="Bound">x</a> <a id="3136" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="3139" href="Chapter.Logic.LessThan.html#3122" class="Bound">x</a> <a id="3141" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="3143" href="Chapter.Logic.LessThan.html#3124" class="Bound">y</a>
    <a id="3149" href="Chapter.Logic.LessThan.html#3112" class="Function">lemma</a> <a id="3155" class="Symbol">{</a><a id="3156" href="Library.Nat.html#48" class="InductiveConstructor">zero</a><a id="3160" class="Symbol">}</a>   <a id="3164" class="Symbol">=</a> <a id="3166" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
    <a id="3178" href="Chapter.Logic.LessThan.html#3112" class="Function">lemma</a> <a id="3184" class="Symbol">{</a><a id="3185" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="3190" class="Symbol">_}</a> <a id="3193" class="Symbol">=</a> <a id="3195" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="3203" href="Chapter.Logic.LessThan.html#3112" class="Function">lemma</a>
</pre>
By performing case analysis on the proof of `x <=ₘ y` we unify `y`
with `x + z`, so our goal turns into providing a proof of `x <= x +
z`. This is done by means of the local `lemma`.

## Inequality is a total order

Here we prove that `<=` is a **total order** on the natural
numbers. We begin by proving **reflexivity**.

<pre class="Agda"><a id="le-refl"></a><a id="3541" href="Chapter.Logic.LessThan.html#3541" class="Function">le-refl</a> <a id="3549" class="Symbol">:</a> <a id="3551" class="Symbol">∀{</a><a id="3553" href="Chapter.Logic.LessThan.html#3553" class="Bound">x</a> <a id="3555" class="Symbol">:</a> <a id="3557" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="3558" class="Symbol">}</a> <a id="3560" class="Symbol">-&gt;</a> <a id="3563" href="Chapter.Logic.LessThan.html#3553" class="Bound">x</a> <a id="3565" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="3568" href="Chapter.Logic.LessThan.html#3553" class="Bound">x</a>
<a id="3570" href="Chapter.Logic.LessThan.html#3541" class="Function">le-refl</a> <a id="3578" class="Symbol">{</a><a id="3579" href="Library.Nat.html#48" class="InductiveConstructor">zero</a><a id="3583" class="Symbol">}</a>   <a id="3587" class="Symbol">=</a> <a id="3589" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
<a id="3597" href="Chapter.Logic.LessThan.html#3541" class="Function">le-refl</a> <a id="3605" class="Symbol">{</a><a id="3606" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="3611" href="Chapter.Logic.LessThan.html#3611" class="Bound">x</a><a id="3612" class="Symbol">}</a> <a id="3614" class="Symbol">=</a> <a id="3616" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="3624" href="Chapter.Logic.LessThan.html#3541" class="Function">le-refl</a>
</pre>
If two numbers are mutually related by `<=`, then they must be
equal. This property is called **antisymmetry** and is proved below.

<pre class="Agda"><a id="le-antisymm"></a><a id="3774" href="Chapter.Logic.LessThan.html#3774" class="Function">le-antisymm</a> <a id="3786" class="Symbol">:</a> <a id="3788" class="Symbol">∀{</a><a id="3790" href="Chapter.Logic.LessThan.html#3790" class="Bound">x</a> <a id="3792" href="Chapter.Logic.LessThan.html#3792" class="Bound">y</a> <a id="3794" class="Symbol">:</a> <a id="3796" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="3797" class="Symbol">}</a> <a id="3799" class="Symbol">-&gt;</a> <a id="3802" href="Chapter.Logic.LessThan.html#3790" class="Bound">x</a> <a id="3804" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="3807" href="Chapter.Logic.LessThan.html#3792" class="Bound">y</a> <a id="3809" class="Symbol">-&gt;</a> <a id="3812" href="Chapter.Logic.LessThan.html#3792" class="Bound">y</a> <a id="3814" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="3817" href="Chapter.Logic.LessThan.html#3790" class="Bound">x</a> <a id="3819" class="Symbol">-&gt;</a> <a id="3822" href="Chapter.Logic.LessThan.html#3790" class="Bound">x</a> <a id="3824" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="3827" href="Chapter.Logic.LessThan.html#3792" class="Bound">y</a>
<a id="3829" href="Chapter.Logic.LessThan.html#3774" class="Function">le-antisymm</a> <a id="3841" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>     <a id="3853" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>     <a id="3865" class="Symbol">=</a> <a id="3867" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="3872" href="Chapter.Logic.LessThan.html#3774" class="Function">le-antisymm</a> <a id="3884" class="Symbol">(</a><a id="3885" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="3893" href="Chapter.Logic.LessThan.html#3893" class="Bound">p</a><a id="3894" class="Symbol">)</a> <a id="3896" class="Symbol">(</a><a id="3897" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="3905" href="Chapter.Logic.LessThan.html#3905" class="Bound">q</a><a id="3906" class="Symbol">)</a> <a id="3908" class="Symbol">=</a> <a id="3910" href="Library.Equality.html#373" class="Function">cong</a> <a id="3915" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="3920" class="Symbol">(</a><a id="3921" href="Chapter.Logic.LessThan.html#3774" class="Function">le-antisymm</a> <a id="3933" href="Chapter.Logic.LessThan.html#3893" class="Bound">p</a> <a id="3935" href="Chapter.Logic.LessThan.html#3905" class="Bound">q</a><a id="3936" class="Symbol">)</a>
</pre>
It is interesting to observe that the case analysis only considers
those combinations in which `x <= y` and `y <= x` are proved by
means of the same constructors. Indeed, when `x <= y` is proved by
`le-zero`, then `x` must be `0` and the only proof of `y <= x` must
have been obtained with `le-zero` as well. Similarly, when `x <= y`
is proved by `le-succ` then `y` must have the form `succ z` for some
`z`, hence the proof of `y <= x` must have been obtained by an
application of `le-succ` too.

Concerning **transitivity**, it is convenient to perform case
analysis on the proofs of `x <= y` and `y <= z`. Note that, when the
former relation is proved by `le-succ`, the second relation can only
be proved by `le-succ` because `y` has the form `succ z`.

<pre class="Agda"><a id="le-trans"></a><a id="4703" href="Chapter.Logic.LessThan.html#4703" class="Function">le-trans</a> <a id="4712" class="Symbol">:</a> <a id="4714" class="Symbol">∀{</a><a id="4716" href="Chapter.Logic.LessThan.html#4716" class="Bound">x</a> <a id="4718" href="Chapter.Logic.LessThan.html#4718" class="Bound">y</a> <a id="4720" href="Chapter.Logic.LessThan.html#4720" class="Bound">z</a> <a id="4722" class="Symbol">:</a> <a id="4724" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="4725" class="Symbol">}</a> <a id="4727" class="Symbol">-&gt;</a> <a id="4730" href="Chapter.Logic.LessThan.html#4716" class="Bound">x</a> <a id="4732" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="4735" href="Chapter.Logic.LessThan.html#4718" class="Bound">y</a> <a id="4737" class="Symbol">-&gt;</a> <a id="4740" href="Chapter.Logic.LessThan.html#4718" class="Bound">y</a> <a id="4742" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="4745" href="Chapter.Logic.LessThan.html#4720" class="Bound">z</a> <a id="4747" class="Symbol">-&gt;</a> <a id="4750" href="Chapter.Logic.LessThan.html#4716" class="Bound">x</a> <a id="4752" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="4755" href="Chapter.Logic.LessThan.html#4720" class="Bound">z</a>
<a id="4757" href="Chapter.Logic.LessThan.html#4703" class="Function">le-trans</a> <a id="4766" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>     <a id="4778" href="Chapter.Logic.LessThan.html#4778" class="Bound">q</a>           <a id="4790" class="Symbol">=</a> <a id="4792" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
<a id="4800" href="Chapter.Logic.LessThan.html#4703" class="Function">le-trans</a> <a id="4809" class="Symbol">(</a><a id="4810" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="4818" href="Chapter.Logic.LessThan.html#4818" class="Bound">p</a><a id="4819" class="Symbol">)</a> <a id="4821" class="Symbol">(</a><a id="4822" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="4830" href="Chapter.Logic.LessThan.html#4830" class="Bound">q</a><a id="4831" class="Symbol">)</a> <a id="4833" class="Symbol">=</a> <a id="4835" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="4843" class="Symbol">(</a><a id="4844" href="Chapter.Logic.LessThan.html#4703" class="Function">le-trans</a> <a id="4853" href="Chapter.Logic.LessThan.html#4818" class="Bound">p</a> <a id="4855" href="Chapter.Logic.LessThan.html#4830" class="Bound">q</a><a id="4856" class="Symbol">)</a>
</pre>
To conclude the proof that `<=` is a total order we have to show
that any two natural numbers `x` and `y` are related in one way or
another. This follows from a straightforward cases analysis on them.

<pre class="Agda"><a id="le-total"></a><a id="5069" href="Chapter.Logic.LessThan.html#5069" class="Function">le-total</a> <a id="5078" class="Symbol">:</a> <a id="5080" class="Symbol">∀(</a><a id="5082" href="Chapter.Logic.LessThan.html#5082" class="Bound">x</a> <a id="5084" href="Chapter.Logic.LessThan.html#5084" class="Bound">y</a> <a id="5086" class="Symbol">:</a> <a id="5088" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="5089" class="Symbol">)</a> <a id="5091" class="Symbol">-&gt;</a> <a id="5094" href="Chapter.Logic.LessThan.html#5082" class="Bound">x</a> <a id="5096" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="5099" href="Chapter.Logic.LessThan.html#5084" class="Bound">y</a> <a id="5101" href="Library.Logic.html#1416" class="Datatype Operator">∨</a> <a id="5103" href="Chapter.Logic.LessThan.html#5084" class="Bound">y</a> <a id="5105" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="5108" href="Chapter.Logic.LessThan.html#5082" class="Bound">x</a>
<a id="5110" href="Chapter.Logic.LessThan.html#5069" class="Function">le-total</a> <a id="5119" href="Library.Nat.html#48" class="InductiveConstructor">zero</a>     <a id="5128" class="Symbol">_</a>    <a id="5133" class="Symbol">=</a> <a id="5135" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="5139" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
<a id="5147" href="Chapter.Logic.LessThan.html#5069" class="Function">le-total</a> <a id="5156" class="Symbol">(</a><a id="5157" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5162" class="Symbol">_)</a> <a id="5165" href="Library.Nat.html#48" class="InductiveConstructor">zero</a> <a id="5170" class="Symbol">=</a> <a id="5172" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="5176" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
<a id="5184" href="Chapter.Logic.LessThan.html#5069" class="Function">le-total</a> <a id="5193" class="Symbol">(</a><a id="5194" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5199" href="Chapter.Logic.LessThan.html#5199" class="Bound">x</a><a id="5200" class="Symbol">)</a> <a id="5202" class="Symbol">(</a><a id="5203" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5208" href="Chapter.Logic.LessThan.html#5208" class="Bound">y</a><a id="5209" class="Symbol">)</a> <a id="5211" class="Symbol">=</a>
  <a id="5215" href="Library.Logic.Laws.html#61" class="Function">∨-elim</a> <a id="5222" class="Symbol">(</a><a id="5223" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="5227" href="Library.Fun.html#112" class="Function Operator">∘</a> <a id="5229" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a><a id="5236" class="Symbol">)</a> <a id="5238" class="Symbol">(</a><a id="5239" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="5243" href="Library.Fun.html#112" class="Function Operator">∘</a> <a id="5245" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a><a id="5252" class="Symbol">)</a> <a id="5254" class="Symbol">(</a><a id="5255" href="Chapter.Logic.LessThan.html#5069" class="Function">le-total</a> <a id="5264" href="Chapter.Logic.LessThan.html#5199" class="Bound">x</a> <a id="5266" href="Chapter.Logic.LessThan.html#5208" class="Bound">y</a><a id="5267" class="Symbol">)</a>
</pre>
## Exercises

1. Show that `<=` is decidable, namely prove the theorem `_<=?_ : ∀(x
   y : ℕ) -> Decidable (x <= y)`.
2. Define `min : ℕ -> ℕ -> ℕ` and `max : ℕ -> ℕ -> ℕ` and prove the theorems
   `le-min : ∀{x y z : ℕ} -> x <= y -> x <= z -> x <= min y z` and `le-max : ∀{x y z : ℕ} -> x <= z -> y <= z -> max x y <= z`.
3. Strict inequality `x < y` can be defined to be the same as `succ x
   <= y`. Prove that this relation is transitive and irreflexive.

<pre class="Agda"><a id="5738" class="Comment">-- EXERCISE 1</a>

<a id="_&lt;=?_"></a><a id="5753" href="Chapter.Logic.LessThan.html#5753" class="Function Operator">_&lt;=?_</a> <a id="5759" class="Symbol">:</a> <a id="5761" class="Symbol">∀(</a><a id="5763" href="Chapter.Logic.LessThan.html#5763" class="Bound">x</a> <a id="5765" href="Chapter.Logic.LessThan.html#5765" class="Bound">y</a> <a id="5767" class="Symbol">:</a> <a id="5769" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="5770" class="Symbol">)</a> <a id="5772" class="Symbol">-&gt;</a> <a id="5775" href="Library.Logic.html#1544" class="Function">Decidable</a> <a id="5785" class="Symbol">(</a><a id="5786" href="Chapter.Logic.LessThan.html#5763" class="Bound">x</a> <a id="5788" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="5791" href="Chapter.Logic.LessThan.html#5765" class="Bound">y</a><a id="5792" class="Symbol">)</a>
<a id="5794" href="Library.Nat.html#48" class="InductiveConstructor">zero</a>   <a id="5801" href="Chapter.Logic.LessThan.html#5753" class="Function Operator">&lt;=?</a> <a id="5805" href="Chapter.Logic.LessThan.html#5805" class="Bound">y</a>    <a id="5810" class="Symbol">=</a> <a id="5812" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="5816" href="Chapter.Logic.LessThan.html#938" class="InductiveConstructor">le-zero</a>
<a id="5824" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5829" href="Chapter.Logic.LessThan.html#5829" class="Bound">x</a> <a id="5831" href="Chapter.Logic.LessThan.html#5753" class="Function Operator">&lt;=?</a> <a id="5835" href="Library.Nat.html#48" class="InductiveConstructor">zero</a> <a id="5840" class="Symbol">=</a> <a id="5842" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="5846" class="Symbol">λ</a> <a id="5848" class="Symbol">()</a>
<a id="5851" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5856" href="Chapter.Logic.LessThan.html#5856" class="Bound">x</a> <a id="5858" href="Chapter.Logic.LessThan.html#5753" class="Function Operator">&lt;=?</a> <a id="5862" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5867" href="Chapter.Logic.LessThan.html#5867" class="Bound">y</a> <a id="5869" class="Keyword">with</a> <a id="5874" href="Chapter.Logic.LessThan.html#5856" class="Bound">x</a> <a id="5876" href="Chapter.Logic.LessThan.html#5753" class="Function Operator">&lt;=?</a> <a id="5880" href="Chapter.Logic.LessThan.html#5867" class="Bound">y</a>
<a id="5882" class="Symbol">...</a> <a id="5886" class="Symbol">|</a> <a id="5888" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="5892" href="Chapter.Logic.LessThan.html#5892" class="Bound">gt</a> <a id="5895" class="Symbol">=</a> <a id="5897" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="5901" class="Symbol">λ</a> <a id="5903" class="Symbol">{</a> <a id="5905" class="Symbol">(</a><a id="5906" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="5914" href="Chapter.Logic.LessThan.html#5914" class="Bound">le</a><a id="5916" class="Symbol">)</a> <a id="5918" class="Symbol">-&gt;</a> <a id="5921" href="Chapter.Logic.LessThan.html#5892" class="Bound">gt</a> <a id="5924" href="Chapter.Logic.LessThan.html#5914" class="Bound">le</a> <a id="5927" class="Symbol">}</a>
<a id="5929" class="Symbol">...</a> <a id="5933" class="Symbol">|</a> <a id="5935" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="5939" href="Chapter.Logic.LessThan.html#5939" class="Bound">le</a> <a id="5942" class="Symbol">=</a> <a id="5944" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="5948" class="Symbol">(</a><a id="5949" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="5957" href="Chapter.Logic.LessThan.html#5939" class="Bound">le</a><a id="5959" class="Symbol">)</a>

<a id="_&lt;_"></a><a id="5962" href="Chapter.Logic.LessThan.html#5962" class="Function Operator">_&lt;_</a> <a id="5966" class="Symbol">:</a> <a id="5968" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="5970" class="Symbol">-&gt;</a> <a id="5973" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="5975" class="Symbol">-&gt;</a> <a id="5978" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="5982" href="Chapter.Logic.LessThan.html#5982" class="Bound">x</a> <a id="5984" href="Chapter.Logic.LessThan.html#5962" class="Function Operator">&lt;</a> <a id="5986" href="Chapter.Logic.LessThan.html#5986" class="Bound">y</a> <a id="5988" class="Symbol">=</a> <a id="5990" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="5995" href="Chapter.Logic.LessThan.html#5982" class="Bound">x</a> <a id="5997" href="Chapter.Logic.LessThan.html#909" class="Datatype Operator">&lt;=</a> <a id="6000" href="Chapter.Logic.LessThan.html#5986" class="Bound">y</a>

<a id="6003" class="Comment">-- EXERCISE 2</a>

<a id="6018" class="Comment">-- ...</a>

<a id="6026" class="Comment">-- EXERCISE 3</a>

<a id="lt-irrefl"></a><a id="6041" href="Chapter.Logic.LessThan.html#6041" class="Function">lt-irrefl</a> <a id="6051" class="Symbol">:</a> <a id="6053" class="Symbol">∀{</a><a id="6055" href="Chapter.Logic.LessThan.html#6055" class="Bound">x</a> <a id="6057" class="Symbol">:</a> <a id="6059" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="6060" class="Symbol">}</a> <a id="6062" class="Symbol">-&gt;</a> <a id="6065" href="Library.Logic.html#1496" class="Function Operator">¬</a> <a id="6067" class="Symbol">(</a><a id="6068" href="Chapter.Logic.LessThan.html#6055" class="Bound">x</a> <a id="6070" href="Chapter.Logic.LessThan.html#5962" class="Function Operator">&lt;</a> <a id="6072" href="Chapter.Logic.LessThan.html#6055" class="Bound">x</a><a id="6073" class="Symbol">)</a>
<a id="6075" href="Chapter.Logic.LessThan.html#6041" class="Function">lt-irrefl</a> <a id="6085" class="Symbol">{</a><a id="6086" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6091" href="Library.Nat.html#48" class="InductiveConstructor">zero</a><a id="6095" class="Symbol">}</a>     <a id="6101" class="Symbol">(</a><a id="6102" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="6110" class="Symbol">())</a>
<a id="6114" href="Chapter.Logic.LessThan.html#6041" class="Function">lt-irrefl</a> <a id="6124" class="Symbol">{</a><a id="6125" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6130" class="Symbol">(</a><a id="6131" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="6136" class="Symbol">_)}</a> <a id="6140" class="Symbol">(</a><a id="6141" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="6149" class="Symbol">(</a><a id="6150" href="Chapter.Logic.LessThan.html#969" class="InductiveConstructor">le-succ</a> <a id="6158" href="Chapter.Logic.LessThan.html#6158" class="Bound">lt</a><a id="6160" class="Symbol">))</a> <a id="6163" class="Symbol">=</a> <a id="6165" href="Chapter.Logic.LessThan.html#6041" class="Function">lt-irrefl</a> <a id="6175" href="Chapter.Logic.LessThan.html#6158" class="Bound">lt</a>

<a id="6179" class="Comment">-- ...</a>
</pre>{:.solution}
