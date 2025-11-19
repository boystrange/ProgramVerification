---
title: Proving properties of Booleans
next:  Chapter.Intro.NaturalNumbers
prev:  Chapter.Intro.Bool
---

<!--
<pre class="Agda"><a id="119" class="Symbol">{-#</a> <a id="123" class="Keyword">OPTIONS</a> <a id="131" class="Pragma">--allow-unsolved-metas</a> <a id="154" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="171" class="Keyword">module</a> <a id="178" href="Chapter.Intro.Bool.Properties.html" class="Module">Chapter.Intro.Bool.Properties</a> <a id="208" class="Keyword">where</a>
</pre>
In this section we start exploring the use of Agda not only as a
language for writing programs, but also as a language for writing
**proofs** about programs.

## Imports

We must be able to express **propositions**, namely assertions that
can be either "true" (if we are able to come up with a proof for
them) or "false" (if we are able to show that every proof of them
leads to a contradiction). In this chapter we will use
**propositional equality**. This relation is not built into Agda,
but is actually [definable as a data
type](Chapter.Logic.Equality.html). For the time being, we simply
*use* the definition of propositional equality from the library
without looking at its definition. To this aim, we *import* the
`Equality` module, along with the previous section from which we
inherit the definition of `Bool` and the functions on boolean
values.

<pre class="Agda"><a id="1081" class="Keyword">open</a> <a id="1086" class="Keyword">import</a> <a id="1093" href="Library.Equality.html" class="Module">Library.Equality</a>
<a id="1110" class="Keyword">open</a> <a id="1115" class="Keyword">import</a> <a id="1122" href="Chapter.Intro.Bool.html" class="Module">Chapter.Intro.Bool</a>
</pre>
## Propositional equality

The first aspect we have to familiarize with is that, unlike the
equality operator that is commonly found in ordinary programming
languages, Agda's propositional equality `==` allows us to build
*types*. More precisely, we can write types such as `true == true`
and `true == false` or, equivalently, `_==_ true true` and `_==_
true false`. An expression of type `true == true` is meant to
represent a *proof* that `true` is equal to `true`, just like an
expression of type `false == false` is meant to represent a *proof*
that `false` is equal to `false`. Understandably, we should be
unable to write expressions of type `true == false` or `false ==
true`, since `true` and `false` are distinct values of type `Bool`
which should be never identified.

The question now is what *is* a proof that `true` is equal to `true`
and, similarly, what is a proof that `false` is equal to
`false`. Recall that, when we have defined the `Bool` data type, we
have also listed all the *values* of type `Bool`, namely `true` and
`false`. In a similar fashion, the `_==_` data type has a
constructor called `refl` (for *reflexivity*) which is a proof of
the fact that any value is equal to itself. We can use `refl` to
write our first theorem about boolean values, namely that `true` is
equal to `true`.

<pre class="Agda"><a id="true-eq"></a><a id="2466" href="Chapter.Intro.Bool.Properties.html#2466" class="Function">true-eq</a> <a id="2474" class="Symbol">:</a> <a id="2476" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="2481" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="2484" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>
<a id="2489" href="Chapter.Intro.Bool.Properties.html#2466" class="Function">true-eq</a> <a id="2497" class="Symbol">=</a> <a id="2499" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>
In a similar fashion, it is easy to prove that `false` is
equal to itself, again using the `refl` constructor:

<pre class="Agda"><a id="false-eq"></a><a id="2625" href="Chapter.Intro.Bool.Properties.html#2625" class="Function">false-eq</a> <a id="2634" class="Symbol">:</a> <a id="2636" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="2642" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="2645" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
<a id="2651" href="Chapter.Intro.Bool.Properties.html#2625" class="Function">false-eq</a> <a id="2660" class="Symbol">=</a> <a id="2662" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>
In general, `refl` can be used to prove any equality of the form `v
== w` where `v` and `w` "are the same". In `true-eq` and `false-eq`
we have taken `v` and `w` to be syntactically the same term, which
resulted in somewhat obvious and rather uninteresting properties. In
general, Agda considers two expressions to be the same if they
evaluate to the same value (technically speaking, if they have the
same normal form). In the previous section we have seen the use of
`C-c C-n` to *normalize* an expression such as `not true`, which
yields `false`. So, `false` is the normal form of `not true`,
meaning that for Agda `not true` and `false` are actually
"equal". This leads to a more interesting result about the behavior
of `not`.

<pre class="Agda"><a id="not-true-eq"></a><a id="3409" href="Chapter.Intro.Bool.Properties.html#3409" class="Function">not-true-eq</a> <a id="3421" class="Symbol">:</a> <a id="3423" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="3427" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="3432" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="3435" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
<a id="3441" href="Chapter.Intro.Bool.Properties.html#3409" class="Function">not-true-eq</a> <a id="3453" class="Symbol">=</a> <a id="3455" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>
Here too we use the `refl` constructor as a proof that `not true`
and `false` are equal. In order to accept this proof, Agda evaluates
`not true` and `false`. The second term is already in normal
form. The first term can be normalized using the definition of
`not`, according to which `not true` yields `false`. This is enough
to conclude that `not true` and `false` are equal.

## Proving that `not` is an involution

Let us now prove that `not` is an involution, namely that `not` is
the inverse function of itself. First of all we have to understand
how to formulate this property. In mathematics we would write the
following predicate:

    ∀(x : Bool) . not (not x) == x

In Agda, we may state this property as the type

    ∀(x : Bool) -> not (not x) == x

which describes a function that, when applied to a value `x` of type
`Bool`, yields a proof that `not (not x)` is equal to `x`. Unlike
the arrow types that we have used until now, this is an example of
**dependent function type** because the type of the codomain of the
function -- `not (not x) == x` -- *depends* the argument `x` to
which the function is applied. The `∀` symbol is purely cosmetic and
may be omitted. We will use it merely for readability.

Going back to our goal, proving that `not` is an involution is the
same as finding a function that has type `∀(x : Bool) -> not (not x)
== x`. That is, our goal is to fill the hole in the following
partial definition:

<pre class="Agda"><a id="not-inv"></a><a id="4910" href="Chapter.Intro.Bool.Properties.html#4910" class="Function">not-inv</a> <a id="4918" class="Symbol">:</a> <a id="4920" class="Symbol">∀(</a><a id="4922" href="Chapter.Intro.Bool.Properties.html#4922" class="Bound">x</a> <a id="4924" class="Symbol">:</a> <a id="4926" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="4930" class="Symbol">)</a> <a id="4932" class="Symbol">-&gt;</a> <a id="4935" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="4939" class="Symbol">(</a><a id="4940" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="4944" href="Chapter.Intro.Bool.Properties.html#4922" class="Bound">x</a><a id="4945" class="Symbol">)</a> <a id="4947" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="4950" href="Chapter.Intro.Bool.Properties.html#4922" class="Bound">x</a>
<a id="4952" href="Chapter.Intro.Bool.Properties.html#4910" class="Function">not-inv</a> <a id="4960" href="Chapter.Intro.Bool.Properties.html#4960" class="Bound">x</a> <a id="4962" class="Symbol">=</a> <a id="4964" class="Hole">{!!}</a>
</pre>
By placing the cursor in the hole and hitting `C-c C-,` we see that
our goal is to provide an expression of type `not (not x) == x`
having at our disposal a value `x` of type `Bool`. At this stage we
might be tempted to fill the hole with `refl`, just like we've done
before for `true-eq`, but if we try to do so Agda will complain with
an error message saying that `not (not x)` and `x` are not the
same. What happens here is that Agda tries to evaluate `not (not x)`
and `x` to see if they have the same normal form. However, since
both contain a variable `x`, which stands for an unknown boolean
value, Agda is unable to reduce these terms any further: `x` is in
normal form, `not (not x)` is in normal form and, for Agda, these
terms are far from being the same.  If `not` is applied to `true`,
then Agda knows that the result is `false`, and if `not` is applied
to `false`, then Agda knows that the result is `true`, but if `not`
is applied to some unknown boolean value `x`, the evaluation of `not
x` (and thus of `not (not x)` as well) is simply stuck.

To make some progress from here we have to recall that `not` has
been defined *by cases* on its argument. The idea then is to proceed
in a similar fashion also for the definition of `not-inv` by
performing a case analysis on `x`.

<pre class="Agda"><a id="not-inv₁"></a><a id="6270" href="Chapter.Intro.Bool.Properties.html#6270" class="Function">not-inv₁</a> <a id="6279" class="Symbol">:</a> <a id="6281" class="Symbol">∀(</a><a id="6283" href="Chapter.Intro.Bool.Properties.html#6283" class="Bound">x</a> <a id="6285" class="Symbol">:</a> <a id="6287" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="6291" class="Symbol">)</a> <a id="6293" class="Symbol">-&gt;</a> <a id="6296" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="6300" class="Symbol">(</a><a id="6301" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="6305" href="Chapter.Intro.Bool.Properties.html#6283" class="Bound">x</a><a id="6306" class="Symbol">)</a> <a id="6308" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="6311" href="Chapter.Intro.Bool.Properties.html#6283" class="Bound">x</a>
<a id="6313" href="Chapter.Intro.Bool.Properties.html#6270" class="Function">not-inv₁</a> <a id="6322" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6328" class="Symbol">=</a> <a id="6330" class="Hole">{!!}</a>
<a id="6335" href="Chapter.Intro.Bool.Properties.html#6270" class="Function">not-inv₁</a> <a id="6344" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6350" class="Symbol">=</a> <a id="6352" class="Hole">{!!}</a>
</pre>
Just like in the definition of `not`, here too we end up with two
equations corresponding to the two possible forms for the argument
`x`. However, something interesting happens in the type of the
function: if we place the cursor in the first hole and hit `C-c C-,`
we see that the goal is now `true == true` instead of `not (not
x)`. What has happened here is that the first hole corresponds to
the case in which `x` is `true`. In this case, Agda is able to
evaluate `not (not x)` to `true` using the definition of `not`. The
good news is that we are now able to provide the proof that `true`
is equal to `true`, that is just `true-eq`. A similar thing happens
for the second hole. In this case, Agda knows that `x` is `false`,
so the goal simplifies to `false == false` for which `false-eq` is a
perfectly valid proof. We have thus completed our first proper
theorem in Agda:

<pre class="Agda"><a id="not-inv₂"></a><a id="7244" href="Chapter.Intro.Bool.Properties.html#7244" class="Function">not-inv₂</a> <a id="7253" class="Symbol">:</a> <a id="7255" class="Symbol">∀(</a><a id="7257" href="Chapter.Intro.Bool.Properties.html#7257" class="Bound">x</a> <a id="7259" class="Symbol">:</a> <a id="7261" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7265" class="Symbol">)</a> <a id="7267" class="Symbol">-&gt;</a> <a id="7270" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="7274" class="Symbol">(</a><a id="7275" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="7279" href="Chapter.Intro.Bool.Properties.html#7257" class="Bound">x</a><a id="7280" class="Symbol">)</a> <a id="7282" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="7285" href="Chapter.Intro.Bool.Properties.html#7257" class="Bound">x</a>
<a id="7287" href="Chapter.Intro.Bool.Properties.html#7244" class="Function">not-inv₂</a> <a id="7296" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7302" class="Symbol">=</a> <a id="7304" href="Chapter.Intro.Bool.Properties.html#2466" class="Function">true-eq</a>
<a id="7312" href="Chapter.Intro.Bool.Properties.html#7244" class="Function">not-inv₂</a> <a id="7321" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7327" class="Symbol">=</a> <a id="7329" href="Chapter.Intro.Bool.Properties.html#2625" class="Function">false-eq</a>
</pre>
Note that, since `true-eq` and `false-eq` are definitionally equal
to `refl`, we could have equivalently written `refl` on the right
hand side of the two equations in the definition of `not-inv₂`.

## Commutativity of `&&` and telescopes

We conclude this chapter with another simple proof concerning the
fact that `&&` is commutative, namely that `x && y == y && x` for
every `x` and `y`.

<pre class="Agda"><a id="&amp;&amp;-comm"></a><a id="7738" href="Chapter.Intro.Bool.Properties.html#7738" class="Function">&amp;&amp;-comm</a> <a id="7746" class="Symbol">:</a> <a id="7748" class="Symbol">∀(</a><a id="7750" href="Chapter.Intro.Bool.Properties.html#7750" class="Bound">x</a> <a id="7752" class="Symbol">:</a> <a id="7754" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7758" class="Symbol">)</a> <a id="7760" class="Symbol">-&gt;</a> <a id="7763" class="Symbol">∀(</a><a id="7765" href="Chapter.Intro.Bool.Properties.html#7765" class="Bound">y</a> <a id="7767" class="Symbol">:</a> <a id="7769" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7773" class="Symbol">)</a> <a id="7775" class="Symbol">-&gt;</a> <a id="7778" href="Chapter.Intro.Bool.Properties.html#7750" class="Bound">x</a> <a id="7780" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7783" href="Chapter.Intro.Bool.Properties.html#7765" class="Bound">y</a> <a id="7785" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="7788" href="Chapter.Intro.Bool.Properties.html#7765" class="Bound">y</a> <a id="7790" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7793" href="Chapter.Intro.Bool.Properties.html#7750" class="Bound">x</a>
<a id="7795" href="Chapter.Intro.Bool.Properties.html#7738" class="Function">&amp;&amp;-comm</a> <a id="7803" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7809" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7815" class="Symbol">=</a> <a id="7817" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7822" href="Chapter.Intro.Bool.Properties.html#7738" class="Function">&amp;&amp;-comm</a> <a id="7830" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7836" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7842" class="Symbol">=</a> <a id="7844" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7849" href="Chapter.Intro.Bool.Properties.html#7738" class="Function">&amp;&amp;-comm</a> <a id="7857" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7863" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7869" class="Symbol">=</a> <a id="7871" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7876" href="Chapter.Intro.Bool.Properties.html#7738" class="Function">&amp;&amp;-comm</a> <a id="7884" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7890" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7896" class="Symbol">=</a> <a id="7898" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>
In this proof we have to perform two independent case analyses, one
for each argument of `&&-comm`. This happens because the `_&&_`
function is defined by case analysis on its first argument so, by
doing case analysis only on `x`, Agda is able to simplify the `x &&
y` part of the goal but not the `y && x` part. Symmetrically, by
doing case analysis only on `y`, Agda is able to simplify the `y &&
x` part of the goal but not the `x && y` part.

We take advantage of this example to illustrate some convenient
syntactic sugar that allows us to write more compact and more
readable types. From the type of `&&-comm` we see that `&&-comm` is
a function that, when applied to two arguments `x` and `y` of type
`Bool`, yields a proof that `x && y == y && x`. In Agda it is not
necessary to write the `->` symbol to separate subsequent arguments
in a dependent function type. That is, the type of `&&-comm` can be
equivalently written as

    &&-comm : ∀(x : Bool) (y : Bool) -> x && y == y && x

Also, where there are multiple subsequent arguments of the same type
in a dependent function type we can collapse them together, like
this:

    &&-comm : ∀(x y : Bool) -> x && y == y && x

This is sometimes referred to as Agda's "telescopic notation". Note
that these types are totally equivalent and therefore
interchangeable.

## Exercises

1. Prove that `true` is both a left and a right unit for `&&`,
   namely that `true && x == x` and `x && true == x` for every
   `x`. Make sure to use case analysis on `x` only if necessary.
2. Prove that `&&` is associative, namely that `x && (y && z) == (x
   && y) && z` for every `x`, `y` and `z`. Make sure to use the
   telescopic notation and case analysis only if necessary.
3. Prove De Morgan's laws for the boolean operators, namely that
   `not (x && y) == not x || not y` and that `not (x || y) == not x
   && not y`.

<pre class="Agda"><a id="9780" class="Comment">-- EXERCISE 1</a>

<a id="9795" class="Comment">-- when proving that x is a left unit for &amp;&amp; it is not necessary to</a>
<a id="9863" class="Comment">-- perform a case analysis on x because, according to the definition</a>
<a id="9932" class="Comment">-- of &amp;&amp;, true &amp;&amp; x is the same as x</a>

<a id="&amp;&amp;-unit-l"></a><a id="9970" href="Chapter.Intro.Bool.Properties.html#9970" class="Function">&amp;&amp;-unit-l</a> <a id="9980" class="Symbol">:</a> <a id="9982" class="Symbol">∀(</a><a id="9984" href="Chapter.Intro.Bool.Properties.html#9984" class="Bound">x</a> <a id="9986" class="Symbol">:</a> <a id="9988" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="9992" class="Symbol">)</a> <a id="9994" class="Symbol">-&gt;</a> <a id="9997" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10002" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10005" href="Chapter.Intro.Bool.Properties.html#9984" class="Bound">x</a> <a id="10007" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10010" href="Chapter.Intro.Bool.Properties.html#9984" class="Bound">x</a>
<a id="10012" href="Chapter.Intro.Bool.Properties.html#9970" class="Function">&amp;&amp;-unit-l</a> <a id="10022" href="Chapter.Intro.Bool.Properties.html#10022" class="Bound">x</a> <a id="10024" class="Symbol">=</a> <a id="10026" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="&amp;&amp;-unit-r"></a><a id="10032" href="Chapter.Intro.Bool.Properties.html#10032" class="Function">&amp;&amp;-unit-r</a> <a id="10042" class="Symbol">:</a> <a id="10044" class="Symbol">∀(</a><a id="10046" href="Chapter.Intro.Bool.Properties.html#10046" class="Bound">x</a> <a id="10048" class="Symbol">:</a> <a id="10050" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10054" class="Symbol">)</a> <a id="10056" class="Symbol">-&gt;</a> <a id="10059" href="Chapter.Intro.Bool.Properties.html#10046" class="Bound">x</a> <a id="10061" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10064" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10069" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10072" href="Chapter.Intro.Bool.Properties.html#10046" class="Bound">x</a>
<a id="10074" href="Chapter.Intro.Bool.Properties.html#10032" class="Function">&amp;&amp;-unit-r</a> <a id="10084" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10090" class="Symbol">=</a> <a id="10092" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10097" href="Chapter.Intro.Bool.Properties.html#10032" class="Function">&amp;&amp;-unit-r</a> <a id="10107" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10113" class="Symbol">=</a> <a id="10115" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="10121" class="Comment">-- EXERCISE 2</a>

<a id="&amp;&amp;-assoc"></a><a id="10136" href="Chapter.Intro.Bool.Properties.html#10136" class="Function">&amp;&amp;-assoc</a> <a id="10145" class="Symbol">:</a> <a id="10147" class="Symbol">∀(</a><a id="10149" href="Chapter.Intro.Bool.Properties.html#10149" class="Bound">x</a> <a id="10151" href="Chapter.Intro.Bool.Properties.html#10151" class="Bound">y</a> <a id="10153" href="Chapter.Intro.Bool.Properties.html#10153" class="Bound">z</a> <a id="10155" class="Symbol">:</a> <a id="10157" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10161" class="Symbol">)</a> <a id="10163" class="Symbol">-&gt;</a> <a id="10166" href="Chapter.Intro.Bool.Properties.html#10149" class="Bound">x</a> <a id="10168" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10171" class="Symbol">(</a><a id="10172" href="Chapter.Intro.Bool.Properties.html#10151" class="Bound">y</a> <a id="10174" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10177" href="Chapter.Intro.Bool.Properties.html#10153" class="Bound">z</a><a id="10178" class="Symbol">)</a> <a id="10180" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10183" class="Symbol">(</a><a id="10184" href="Chapter.Intro.Bool.Properties.html#10149" class="Bound">x</a> <a id="10186" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10189" href="Chapter.Intro.Bool.Properties.html#10151" class="Bound">y</a><a id="10190" class="Symbol">)</a> <a id="10192" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10195" href="Chapter.Intro.Bool.Properties.html#10153" class="Bound">z</a>
<a id="10197" href="Chapter.Intro.Bool.Properties.html#10136" class="Function">&amp;&amp;-assoc</a> <a id="10206" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10211" href="Chapter.Intro.Bool.Properties.html#10211" class="Bound">y</a> <a id="10213" href="Chapter.Intro.Bool.Properties.html#10213" class="Bound">z</a> <a id="10215" class="Symbol">=</a> <a id="10217" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10222" href="Chapter.Intro.Bool.Properties.html#10136" class="Function">&amp;&amp;-assoc</a> <a id="10231" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10237" href="Chapter.Intro.Bool.Properties.html#10237" class="Bound">y</a> <a id="10239" href="Chapter.Intro.Bool.Properties.html#10239" class="Bound">z</a> <a id="10241" class="Symbol">=</a> <a id="10243" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="10249" class="Comment">-- EXERCISE 3</a>

<a id="not-&amp;&amp;"></a><a id="10264" href="Chapter.Intro.Bool.Properties.html#10264" class="Function">not-&amp;&amp;</a> <a id="10271" class="Symbol">:</a> <a id="10273" class="Symbol">∀(</a><a id="10275" href="Chapter.Intro.Bool.Properties.html#10275" class="Bound">x</a> <a id="10277" href="Chapter.Intro.Bool.Properties.html#10277" class="Bound">y</a> <a id="10279" class="Symbol">:</a> <a id="10281" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10285" class="Symbol">)</a> <a id="10287" class="Symbol">-&gt;</a> <a id="10290" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10294" class="Symbol">(</a><a id="10295" href="Chapter.Intro.Bool.Properties.html#10275" class="Bound">x</a> <a id="10297" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10300" href="Chapter.Intro.Bool.Properties.html#10277" class="Bound">y</a><a id="10301" class="Symbol">)</a> <a id="10303" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10306" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10310" href="Chapter.Intro.Bool.Properties.html#10275" class="Bound">x</a> <a id="10312" href="Chapter.Intro.Bool.html#9948" class="Function Operator">||</a> <a id="10315" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10319" href="Chapter.Intro.Bool.Properties.html#10277" class="Bound">y</a>
<a id="10321" href="Chapter.Intro.Bool.Properties.html#10264" class="Function">not-&amp;&amp;</a> <a id="10328" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10334" class="Symbol">_</a> <a id="10336" class="Symbol">=</a> <a id="10338" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10343" href="Chapter.Intro.Bool.Properties.html#10264" class="Function">not-&amp;&amp;</a> <a id="10350" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10356" class="Symbol">_</a> <a id="10358" class="Symbol">=</a> <a id="10360" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="not-||"></a><a id="10366" href="Chapter.Intro.Bool.Properties.html#10366" class="Function">not-||</a> <a id="10373" class="Symbol">:</a> <a id="10375" class="Symbol">∀(</a><a id="10377" href="Chapter.Intro.Bool.Properties.html#10377" class="Bound">x</a> <a id="10379" href="Chapter.Intro.Bool.Properties.html#10379" class="Bound">y</a> <a id="10381" class="Symbol">:</a> <a id="10383" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10387" class="Symbol">)</a> <a id="10389" class="Symbol">-&gt;</a> <a id="10392" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10396" class="Symbol">(</a><a id="10397" href="Chapter.Intro.Bool.Properties.html#10377" class="Bound">x</a> <a id="10399" href="Chapter.Intro.Bool.html#9948" class="Function Operator">||</a> <a id="10402" href="Chapter.Intro.Bool.Properties.html#10379" class="Bound">y</a><a id="10403" class="Symbol">)</a> <a id="10405" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10408" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10412" href="Chapter.Intro.Bool.Properties.html#10377" class="Bound">x</a> <a id="10414" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10417" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10421" href="Chapter.Intro.Bool.Properties.html#10379" class="Bound">y</a>
<a id="10423" href="Chapter.Intro.Bool.Properties.html#10366" class="Function">not-||</a> <a id="10430" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10436" class="Symbol">_</a> <a id="10438" class="Symbol">=</a> <a id="10440" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10445" href="Chapter.Intro.Bool.Properties.html#10366" class="Function">not-||</a> <a id="10452" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10458" class="Symbol">_</a> <a id="10460" class="Symbol">=</a> <a id="10462" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>{:.solution}
