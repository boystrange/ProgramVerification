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
function -- `not (not x) == x` -- *depends* on the argument `x` to
which the function is applied. The `∀` symbol is purely cosmetic and
may be omitted. We will use it merely for readability.

Going back to our goal, proving that `not` is an involution is the
same as finding a function that has type `∀(x : Bool) -> not (not x)
== x`. That is, our goal is to fill the hole in the following
partial definition:

<pre class="Agda"><a id="not-inv"></a><a id="4913" href="Chapter.Intro.Bool.Properties.html#4913" class="Function">not-inv</a> <a id="4921" class="Symbol">:</a> <a id="4923" class="Symbol">∀(</a><a id="4925" href="Chapter.Intro.Bool.Properties.html#4925" class="Bound">x</a> <a id="4927" class="Symbol">:</a> <a id="4929" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="4933" class="Symbol">)</a> <a id="4935" class="Symbol">-&gt;</a> <a id="4938" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="4942" class="Symbol">(</a><a id="4943" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="4947" href="Chapter.Intro.Bool.Properties.html#4925" class="Bound">x</a><a id="4948" class="Symbol">)</a> <a id="4950" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="4953" href="Chapter.Intro.Bool.Properties.html#4925" class="Bound">x</a>
<a id="4955" href="Chapter.Intro.Bool.Properties.html#4913" class="Function">not-inv</a> <a id="4963" href="Chapter.Intro.Bool.Properties.html#4963" class="Bound">x</a> <a id="4965" class="Symbol">=</a> <a id="4967" class="Hole">{!!}</a>
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

<pre class="Agda"><a id="not-inv₁"></a><a id="6273" href="Chapter.Intro.Bool.Properties.html#6273" class="Function">not-inv₁</a> <a id="6282" class="Symbol">:</a> <a id="6284" class="Symbol">∀(</a><a id="6286" href="Chapter.Intro.Bool.Properties.html#6286" class="Bound">x</a> <a id="6288" class="Symbol">:</a> <a id="6290" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="6294" class="Symbol">)</a> <a id="6296" class="Symbol">-&gt;</a> <a id="6299" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="6303" class="Symbol">(</a><a id="6304" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="6308" href="Chapter.Intro.Bool.Properties.html#6286" class="Bound">x</a><a id="6309" class="Symbol">)</a> <a id="6311" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="6314" href="Chapter.Intro.Bool.Properties.html#6286" class="Bound">x</a>
<a id="6316" href="Chapter.Intro.Bool.Properties.html#6273" class="Function">not-inv₁</a> <a id="6325" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6331" class="Symbol">=</a> <a id="6333" class="Hole">{!!}</a>
<a id="6338" href="Chapter.Intro.Bool.Properties.html#6273" class="Function">not-inv₁</a> <a id="6347" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6353" class="Symbol">=</a> <a id="6355" class="Hole">{!!}</a>
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

<pre class="Agda"><a id="not-inv₂"></a><a id="7247" href="Chapter.Intro.Bool.Properties.html#7247" class="Function">not-inv₂</a> <a id="7256" class="Symbol">:</a> <a id="7258" class="Symbol">∀(</a><a id="7260" href="Chapter.Intro.Bool.Properties.html#7260" class="Bound">x</a> <a id="7262" class="Symbol">:</a> <a id="7264" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7268" class="Symbol">)</a> <a id="7270" class="Symbol">-&gt;</a> <a id="7273" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="7277" class="Symbol">(</a><a id="7278" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="7282" href="Chapter.Intro.Bool.Properties.html#7260" class="Bound">x</a><a id="7283" class="Symbol">)</a> <a id="7285" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="7288" href="Chapter.Intro.Bool.Properties.html#7260" class="Bound">x</a>
<a id="7290" href="Chapter.Intro.Bool.Properties.html#7247" class="Function">not-inv₂</a> <a id="7299" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7305" class="Symbol">=</a> <a id="7307" href="Chapter.Intro.Bool.Properties.html#2466" class="Function">true-eq</a>
<a id="7315" href="Chapter.Intro.Bool.Properties.html#7247" class="Function">not-inv₂</a> <a id="7324" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7330" class="Symbol">=</a> <a id="7332" href="Chapter.Intro.Bool.Properties.html#2625" class="Function">false-eq</a>
</pre>
Note that, since `true-eq` and `false-eq` are definitionally equal
to `refl`, we could have equivalently written `refl` on the right
hand side of the two equations in the definition of `not-inv₂`.

## Commutativity of `&&` and telescopes

We conclude this chapter with another simple proof concerning the
fact that `&&` is commutative, namely that `x && y == y && x` for
every `x` and `y`.

<pre class="Agda"><a id="&amp;&amp;-comm"></a><a id="7741" href="Chapter.Intro.Bool.Properties.html#7741" class="Function">&amp;&amp;-comm</a> <a id="7749" class="Symbol">:</a> <a id="7751" class="Symbol">∀(</a><a id="7753" href="Chapter.Intro.Bool.Properties.html#7753" class="Bound">x</a> <a id="7755" class="Symbol">:</a> <a id="7757" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7761" class="Symbol">)</a> <a id="7763" class="Symbol">-&gt;</a> <a id="7766" class="Symbol">∀(</a><a id="7768" href="Chapter.Intro.Bool.Properties.html#7768" class="Bound">y</a> <a id="7770" class="Symbol">:</a> <a id="7772" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="7776" class="Symbol">)</a> <a id="7778" class="Symbol">-&gt;</a> <a id="7781" href="Chapter.Intro.Bool.Properties.html#7753" class="Bound">x</a> <a id="7783" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7786" href="Chapter.Intro.Bool.Properties.html#7768" class="Bound">y</a> <a id="7788" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="7791" href="Chapter.Intro.Bool.Properties.html#7768" class="Bound">y</a> <a id="7793" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7796" href="Chapter.Intro.Bool.Properties.html#7753" class="Bound">x</a>
<a id="7798" href="Chapter.Intro.Bool.Properties.html#7741" class="Function">&amp;&amp;-comm</a> <a id="7806" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7812" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7818" class="Symbol">=</a> <a id="7820" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7825" href="Chapter.Intro.Bool.Properties.html#7741" class="Function">&amp;&amp;-comm</a> <a id="7833" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7839" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7845" class="Symbol">=</a> <a id="7847" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7852" href="Chapter.Intro.Bool.Properties.html#7741" class="Function">&amp;&amp;-comm</a> <a id="7860" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7866" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7872" class="Symbol">=</a> <a id="7874" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="7879" href="Chapter.Intro.Bool.Properties.html#7741" class="Function">&amp;&amp;-comm</a> <a id="7887" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7893" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7899" class="Symbol">=</a> <a id="7901" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
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

<pre class="Agda"><a id="9783" class="Comment">-- EXERCISE 1</a>

<a id="9798" class="Comment">-- when proving that x is a left unit for &amp;&amp; it is not necessary to</a>
<a id="9866" class="Comment">-- perform a case analysis on x because, according to the definition</a>
<a id="9935" class="Comment">-- of &amp;&amp;, true &amp;&amp; x is the same as x</a>

<a id="&amp;&amp;-unit-l"></a><a id="9973" href="Chapter.Intro.Bool.Properties.html#9973" class="Function">&amp;&amp;-unit-l</a> <a id="9983" class="Symbol">:</a> <a id="9985" class="Symbol">∀(</a><a id="9987" href="Chapter.Intro.Bool.Properties.html#9987" class="Bound">x</a> <a id="9989" class="Symbol">:</a> <a id="9991" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="9995" class="Symbol">)</a> <a id="9997" class="Symbol">-&gt;</a> <a id="10000" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10005" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10008" href="Chapter.Intro.Bool.Properties.html#9987" class="Bound">x</a> <a id="10010" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10013" href="Chapter.Intro.Bool.Properties.html#9987" class="Bound">x</a>
<a id="10015" href="Chapter.Intro.Bool.Properties.html#9973" class="Function">&amp;&amp;-unit-l</a> <a id="10025" href="Chapter.Intro.Bool.Properties.html#10025" class="Bound">x</a> <a id="10027" class="Symbol">=</a> <a id="10029" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="&amp;&amp;-unit-r"></a><a id="10035" href="Chapter.Intro.Bool.Properties.html#10035" class="Function">&amp;&amp;-unit-r</a> <a id="10045" class="Symbol">:</a> <a id="10047" class="Symbol">∀(</a><a id="10049" href="Chapter.Intro.Bool.Properties.html#10049" class="Bound">x</a> <a id="10051" class="Symbol">:</a> <a id="10053" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10057" class="Symbol">)</a> <a id="10059" class="Symbol">-&gt;</a> <a id="10062" href="Chapter.Intro.Bool.Properties.html#10049" class="Bound">x</a> <a id="10064" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10067" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10072" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10075" href="Chapter.Intro.Bool.Properties.html#10049" class="Bound">x</a>
<a id="10077" href="Chapter.Intro.Bool.Properties.html#10035" class="Function">&amp;&amp;-unit-r</a> <a id="10087" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10093" class="Symbol">=</a> <a id="10095" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10100" href="Chapter.Intro.Bool.Properties.html#10035" class="Function">&amp;&amp;-unit-r</a> <a id="10110" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10116" class="Symbol">=</a> <a id="10118" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="10124" class="Comment">-- EXERCISE 2</a>

<a id="&amp;&amp;-assoc"></a><a id="10139" href="Chapter.Intro.Bool.Properties.html#10139" class="Function">&amp;&amp;-assoc</a> <a id="10148" class="Symbol">:</a> <a id="10150" class="Symbol">∀(</a><a id="10152" href="Chapter.Intro.Bool.Properties.html#10152" class="Bound">x</a> <a id="10154" href="Chapter.Intro.Bool.Properties.html#10154" class="Bound">y</a> <a id="10156" href="Chapter.Intro.Bool.Properties.html#10156" class="Bound">z</a> <a id="10158" class="Symbol">:</a> <a id="10160" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10164" class="Symbol">)</a> <a id="10166" class="Symbol">-&gt;</a> <a id="10169" href="Chapter.Intro.Bool.Properties.html#10152" class="Bound">x</a> <a id="10171" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10174" class="Symbol">(</a><a id="10175" href="Chapter.Intro.Bool.Properties.html#10154" class="Bound">y</a> <a id="10177" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10180" href="Chapter.Intro.Bool.Properties.html#10156" class="Bound">z</a><a id="10181" class="Symbol">)</a> <a id="10183" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10186" class="Symbol">(</a><a id="10187" href="Chapter.Intro.Bool.Properties.html#10152" class="Bound">x</a> <a id="10189" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10192" href="Chapter.Intro.Bool.Properties.html#10154" class="Bound">y</a><a id="10193" class="Symbol">)</a> <a id="10195" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10198" href="Chapter.Intro.Bool.Properties.html#10156" class="Bound">z</a>
<a id="10200" href="Chapter.Intro.Bool.Properties.html#10139" class="Function">&amp;&amp;-assoc</a> <a id="10209" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a> <a id="10214" href="Chapter.Intro.Bool.Properties.html#10214" class="Bound">y</a> <a id="10216" href="Chapter.Intro.Bool.Properties.html#10216" class="Bound">z</a> <a id="10218" class="Symbol">=</a> <a id="10220" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10225" href="Chapter.Intro.Bool.Properties.html#10139" class="Function">&amp;&amp;-assoc</a> <a id="10234" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10240" href="Chapter.Intro.Bool.Properties.html#10240" class="Bound">y</a> <a id="10242" href="Chapter.Intro.Bool.Properties.html#10242" class="Bound">z</a> <a id="10244" class="Symbol">=</a> <a id="10246" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="10252" class="Comment">-- EXERCISE 3</a>

<a id="not-&amp;&amp;"></a><a id="10267" href="Chapter.Intro.Bool.Properties.html#10267" class="Function">not-&amp;&amp;</a> <a id="10274" class="Symbol">:</a> <a id="10276" class="Symbol">∀(</a><a id="10278" href="Chapter.Intro.Bool.Properties.html#10278" class="Bound">x</a> <a id="10280" href="Chapter.Intro.Bool.Properties.html#10280" class="Bound">y</a> <a id="10282" class="Symbol">:</a> <a id="10284" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10288" class="Symbol">)</a> <a id="10290" class="Symbol">-&gt;</a> <a id="10293" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10297" class="Symbol">(</a><a id="10298" href="Chapter.Intro.Bool.Properties.html#10278" class="Bound">x</a> <a id="10300" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10303" href="Chapter.Intro.Bool.Properties.html#10280" class="Bound">y</a><a id="10304" class="Symbol">)</a> <a id="10306" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10309" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10313" href="Chapter.Intro.Bool.Properties.html#10278" class="Bound">x</a> <a id="10315" href="Chapter.Intro.Bool.html#9948" class="Function Operator">||</a> <a id="10318" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10322" href="Chapter.Intro.Bool.Properties.html#10280" class="Bound">y</a>
<a id="10324" href="Chapter.Intro.Bool.Properties.html#10267" class="Function">not-&amp;&amp;</a> <a id="10331" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10337" class="Symbol">_</a> <a id="10339" class="Symbol">=</a> <a id="10341" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10346" href="Chapter.Intro.Bool.Properties.html#10267" class="Function">not-&amp;&amp;</a> <a id="10353" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10359" class="Symbol">_</a> <a id="10361" class="Symbol">=</a> <a id="10363" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>

<a id="not-||"></a><a id="10369" href="Chapter.Intro.Bool.Properties.html#10369" class="Function">not-||</a> <a id="10376" class="Symbol">:</a> <a id="10378" class="Symbol">∀(</a><a id="10380" href="Chapter.Intro.Bool.Properties.html#10380" class="Bound">x</a> <a id="10382" href="Chapter.Intro.Bool.Properties.html#10382" class="Bound">y</a> <a id="10384" class="Symbol">:</a> <a id="10386" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a><a id="10390" class="Symbol">)</a> <a id="10392" class="Symbol">-&gt;</a> <a id="10395" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10399" class="Symbol">(</a><a id="10400" href="Chapter.Intro.Bool.Properties.html#10380" class="Bound">x</a> <a id="10402" href="Chapter.Intro.Bool.html#9948" class="Function Operator">||</a> <a id="10405" href="Chapter.Intro.Bool.Properties.html#10382" class="Bound">y</a><a id="10406" class="Symbol">)</a> <a id="10408" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="10411" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10415" href="Chapter.Intro.Bool.Properties.html#10380" class="Bound">x</a> <a id="10417" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="10420" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10424" href="Chapter.Intro.Bool.Properties.html#10382" class="Bound">y</a>
<a id="10426" href="Chapter.Intro.Bool.Properties.html#10369" class="Function">not-||</a> <a id="10433" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10439" class="Symbol">_</a> <a id="10441" class="Symbol">=</a> <a id="10443" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="10448" href="Chapter.Intro.Bool.Properties.html#10369" class="Function">not-||</a> <a id="10455" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10461" class="Symbol">_</a> <a id="10463" class="Symbol">=</a> <a id="10465" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
</pre>{:.solution}
