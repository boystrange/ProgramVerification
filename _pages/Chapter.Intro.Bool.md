---
title: "Inductive data types: the Booleans"
next:  Chapter.Intro.Bool.Properties
prev:  Chapter.Intro.Lambda
---

<!--
<pre class="Agda"><a id="128" class="Symbol">{-#</a> <a id="132" class="Keyword">OPTIONS</a> <a id="140" class="Pragma">--allow-unsolved-metas</a> <a id="163" class="Symbol">#-}</a>
</pre>-->

<pre class="Agda"><a id="180" class="Keyword">module</a> <a id="187" href="Chapter.Intro.Bool.html" class="Module">Chapter.Intro.Bool</a> <a id="206" class="Keyword">where</a>
</pre>
In this chapter we start looking at the constructs for defining and
using new data types in Agda.

## Defining simple data types

<pre class="Agda"><a id="351" class="Keyword">data</a> <a id="Bool"></a><a id="356" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="361" class="Symbol">:</a> <a id="363" href="Agda.Primitive.html#388" class="Primitive">Set</a> <a id="367" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="375" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="381" class="Symbol">:</a> <a id="383" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="390" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="396" class="Symbol">:</a> <a id="398" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
</pre>
A new data type definition begins with the keyword `data` followed
by the name of the data type we are defining (`Bool` in this case)
and by its signature. The signature of `Bool` states that `Bool` is
an Agda `Set`, that is the simplest form for data type we can
define. In later sections we will define increasingly more complex
data types having more sophisticated signatures.

After the signature is the keyword `where` followed by a list of
**constructors**. For a simple data type like `Bool`, the
constructors effectively enumerate all the possible values of that
type. In this case, the only values of type `Bool` are `true` and
`false`.

It is important to stress that a new data type defines two distinct
entities: a new type name (`Bool`) which is different from any other
type that has been previously defined; a set of values of that type,
which is the smallest set of terms that can be built using the
provided constructors. When we say "value" we mean an expression
that cannot be reduced any further. However, there can be
expressions that are different from `true` and `false` and yet that
happen to have type `Bool` because, once evaluated, they yield a
value that is either `true` or `false`.

We can verify these claims asking Agda to type all the entities
introduced by the above definition: the command `C-c C-d Bool`
yields `Set`, and the commands `C-c C-d true` and `C-c C-d false`
both yield `Bool`.

## Defining functions using pattern matching

Let us now define the function that *negates* a boolean value. Its
type is

<pre class="Agda"><a id="not"></a><a id="1960" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="1964" class="Symbol">:</a> <a id="1966" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="1971" class="Symbol">-&gt;</a> <a id="1974" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
</pre>
and its definition is given by cases on all the boolean values:

<pre class="Agda"><a id="2053" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="2057" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="2063" class="Symbol">=</a> <a id="2065" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
<a id="2071" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="2075" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="2081" class="Symbol">=</a> <a id="2083" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>
</pre>
Note that we are providing several *equations* for `not`, one for
each possible constructor for `Bool`, along with a corresponding
expression (on the right hand side of the `=` sign) showing what the
function yields when applied to a particular boolean value. As
always when we use the symbol `=`, we are telling Agda that `not
true` is definitionally equal to `false` and that `not false` is
definitionally equal to `true`. By "definitionally equal" we mean
that these terms are interchangeable: one may be used where the
other is expected without Agda noticing any difference.

We can ask Agda to *infer* the type of an application such as `not
true` or `not false` by entering `C-c C-d not true` or `C-c C-d not
false`. In both cases Agda answers `Bool`, meaning that both `not
true` and `not false` are expressions of type `Bool`, namely
expressions that, once evaluated, yield either `true` or `false`. In
fact, we can also ask Agda to evaluate the application of `not` to a
boolean value by entering `C-c C-n` (the `n` in `C-n` abbreviates
"normalize", which is the technical term to indicate the evaluation
process). We see that `not true` evaluates to `false` and `not
false` evaluates to `true`, in accordance with the definition of
`not`.

We will extensively use this style of defining functions by case
analysis on their arguments. In fact, Agda provides a convenient
facility for generating all the cases we have to consider in an
interactive way by starting from an *incomplete* definition of `not`
(as usual, we use indices such as `₁` and `₂` to distinguish
multiple definitions of the same function so that they are not in
conflict with each other).

    not₁ : Bool -> Bool
    not₁ x = ?

We can place the question mark `?` anywhere an expression is
expected and we do not know yet which expression it should be. Once
we have done that, by loading the file with `C-c C-l` the question
mark turns into a **hole**.

<pre class="Agda"><a id="not₁"></a><a id="4030" href="Chapter.Intro.Bool.html#4030" class="Function">not₁</a> <a id="4035" class="Symbol">:</a> <a id="4037" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="4042" class="Symbol">-&gt;</a> <a id="4045" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="4050" href="Chapter.Intro.Bool.html#4030" class="Function">not₁</a> <a id="4055" href="Chapter.Intro.Bool.html#4055" class="Bound">x</a> <a id="4057" class="Symbol">=</a> <a id="4059" class="Hole">{!!}</a>
</pre>
By placing the cursor in the hole and hitting `C-c C-,` we can ask
Agda for help on how to proceed. Agda will tell us that we are
supposed to fill the hole with an expression of type `Bool` and also
that, in order to do so, we have at our disposal a value `x`, the
argument of `not₁`, which is also of type `Bool`. Since the result
of `not₁` *depends* on `x`, we have to perform a case analysis on it
by entering `C-c C-c x`. Agda knows that `x` is of type `Bool` and
that the only values of that type are `true` and `false`, so Agda
will create two equations corresponding to the two cases we have to
handle.

<pre class="Agda"><a id="not₂"></a><a id="4684" href="Chapter.Intro.Bool.html#4684" class="Function">not₂</a> <a id="4689" class="Symbol">:</a> <a id="4691" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="4696" class="Symbol">-&gt;</a> <a id="4699" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="4704" href="Chapter.Intro.Bool.html#4684" class="Function">not₂</a> <a id="4709" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="4715" class="Symbol">=</a> <a id="4717" class="Hole">{!!}</a>
<a id="4722" href="Chapter.Intro.Bool.html#4684" class="Function">not₂</a> <a id="4727" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="4733" class="Symbol">=</a> <a id="4735" class="Hole">{!!}</a>
</pre>
We now have two holes to fill with expressions of type `Bool`. When
there is more than one hole, we can use `C-c C-f` and `C-c C-b` to
move forward and backward from one hole to the next or to the
previous one. By placing the cursor in the first hole we can enter
`false` followed by `C-c C-SPACE` to fill the hole with the provided
expression. Once we've also filled the second hole with `true` we
have completed the definition of `not₂`.

As an example of boolean function on two arguments, let us now
define the boolean conjunction.

<pre class="Agda"><a id="and"></a><a id="5286" href="Chapter.Intro.Bool.html#5286" class="Function">and</a> <a id="5290" class="Symbol">:</a> <a id="5292" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="5297" class="Symbol">-&gt;</a> <a id="5300" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="5305" class="Symbol">-&gt;</a> <a id="5308" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="5313" href="Chapter.Intro.Bool.html#5286" class="Function">and</a> <a id="5317" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="5323" href="Chapter.Intro.Bool.html#5323" class="Bound">y</a> <a id="5325" class="Symbol">=</a> <a id="5327" href="Chapter.Intro.Bool.html#5323" class="Bound">y</a>
<a id="5329" href="Chapter.Intro.Bool.html#5286" class="Function">and</a> <a id="5333" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="5339" class="Symbol">_</a> <a id="5341" class="Symbol">=</a> <a id="5343" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
</pre>
Since `true` is the unit of boolean conjunction, when the first
argument of `and` is `true` the result is just the second
argument. Since `false` is the absorbing element of the boolean
conjunction, when the first argument of `and` is `false` the result
is simply `false` regardless of the second argument. When an
argument is not used in an equation, we can replace it with an
underscore `_`. It is not necessary to do so, but using underscores
on the left hand side of equations sometimes helps us keeping the
code clean and easier to read, highlighting the fact that some
arguments are not used in some cases.

We can ask Agda to evaluate `and` applied to some inputs to convince
ourselves that the function behaves as expected. For example, `C-c
C-n and true true` yields `true` whereas `C-c C-n and false true`
yields `false`.

Note that the above definition of `and` is not the only way to
define boolean conjunction. In fact, we could as well provide four
equations, one for each combination of inputs:

<pre class="Agda"><a id="and₁"></a><a id="6369" href="Chapter.Intro.Bool.html#6369" class="Function">and₁</a> <a id="6374" class="Symbol">:</a> <a id="6376" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="6381" class="Symbol">-&gt;</a> <a id="6384" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="6389" class="Symbol">-&gt;</a> <a id="6392" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="6397" href="Chapter.Intro.Bool.html#6369" class="Function">and₁</a> <a id="6402" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6408" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6414" class="Symbol">=</a> <a id="6416" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>
<a id="6421" href="Chapter.Intro.Bool.html#6369" class="Function">and₁</a> <a id="6426" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6432" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6438" class="Symbol">=</a> <a id="6440" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
<a id="6446" href="Chapter.Intro.Bool.html#6369" class="Function">and₁</a> <a id="6451" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6457" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="6463" class="Symbol">=</a> <a id="6465" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
<a id="6471" href="Chapter.Intro.Bool.html#6369" class="Function">and₁</a> <a id="6476" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6482" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="6488" class="Symbol">=</a> <a id="6490" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
</pre>
As usual, there are many different ways in which functions can be
defined. However, in Agda the definition we choose for a function is
more important than ever because it may heavily affect how we prove
properties about it as we will see shortly.

## Infix notation

Agda applications can be arbitrarily nested. For example, we can
express the conjunction of `true` with the result of the conjunction
of `true` and `false` by means of the expression `and true (and true
false)` which evaluates to `false`. This notation, in which a
function application is denoted by the function *followed by* its
arguments, is sometimes called **prefix notation** and is widespread
in most programming languages. Sometimes it is desirable to
introduce a more lightweight and possibly more familiar notation for
function applications whereby a function with two arguments is
placed *in between* its arguments. Agda provides a sophisticated
mechanism to define such notation, in which the programmer specifies
the syntactic location of the arguments of a function by means of
underscores. For example, the following is an alternative, but fully
equivalent definition of `and` as the binary operator `&&` as found
in other programming languages.

<pre class="Agda"><a id="_&amp;&amp;_"></a><a id="7734" href="Chapter.Intro.Bool.html#7734" class="Function Operator">_&amp;&amp;_</a> <a id="7739" class="Symbol">:</a> <a id="7741" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="7746" class="Symbol">-&gt;</a> <a id="7749" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="7754" class="Symbol">-&gt;</a> <a id="7757" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="7762" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="7768" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7771" href="Chapter.Intro.Bool.html#7771" class="Bound">y</a> <a id="7773" class="Symbol">=</a> <a id="7775" href="Chapter.Intro.Bool.html#7771" class="Bound">y</a>
<a id="7777" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="7783" href="Chapter.Intro.Bool.html#7734" class="Function Operator">&amp;&amp;</a> <a id="7786" class="Symbol">_</a> <a id="7788" class="Symbol">=</a> <a id="7790" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>
</pre>
With this definition in place, we can write e.g. `true && (true &&
false)` instead of `and true (and true false)`. The two underscores
in `_&&_` are still part of the name of the function we are
defining, although they are omitted when `&&` is used as an infix
operator. We can still refer to `&&` as a function by explicitly
writing the underscores. For example, `_&&_ true (_&&_ true false)`
is yet another way of writing `true && (true && false)`.

A problem remains in that it is still not possible to write an
expression such as `true && true && false`. The problem here is that
Agda does not know whether this expression is meant to be
interpreted as `true && (true && false)` or as `(true && true) &&
false`. We can provide this information by means of a *fixity
declaration* of the form

<pre class="Agda"><a id="8601" class="Keyword">infixl</a> <a id="8608" class="Number">6</a> <a id="8610" href="Chapter.Intro.Bool.html#7734" class="Function Operator">_&amp;&amp;_</a>
</pre>
telling Agda that `&&` is meant to be interpreted as a
*left-associative* operator with priority `6`. We would use `infixr`
for declaring *right-associative* operators and just `infix` for
declaring operators that are neither left- nor right-associative
(typically, these will be operators with just one operand or more
than two operands). The priority becomes important as soon as more
than one operator is defined to tell Agda what is the intended
priority among them.

## Exercises

1. Redefine `and` interactively by case splitting on its first argument.
2. Redefine `and` interactively by case splitting on its second argument.
3. Define the function `_||_ : Bool -> Bool -> Bool` that computes
   the *disjunction* of two boolean values. Make sure that the
   function behaves as expected by testing it on all possible
   inputs.
4. Provide a fixity declaration for `_||_` so that it is left
   associative and has priority smaller than that of `&&`. Use `C-c
   C-n` to convince yourself that the priorities given to `&&` and
   `||` work as expected.
5. Define the function `xor : Bool -> Bool -> Bool` that computes
   the exclusive or of two boolean values. Is it possible to define
   `xor` using just two equations?

<pre class="Agda"><a id="9853" class="Comment">-- EXERCISE 1</a>
<a id="and₂"></a><a id="9867" href="Chapter.Intro.Bool.html#9867" class="Function">and₂</a> <a id="9872" class="Symbol">:</a> <a id="9874" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="9879" class="Symbol">-&gt;</a> <a id="9882" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="9887" class="Symbol">-&gt;</a> <a id="9890" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="9895" href="Chapter.Intro.Bool.html#9867" class="Function">and₂</a> <a id="9900" href="Chapter.Intro.Bool.html#9900" class="Bound">x</a> <a id="9902" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="9908" class="Symbol">=</a> <a id="9910" href="Chapter.Intro.Bool.html#9900" class="Bound">x</a>
<a id="9912" href="Chapter.Intro.Bool.html#9867" class="Function">and₂</a> <a id="9917" class="Symbol">_</a> <a id="9919" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="9925" class="Symbol">=</a> <a id="9927" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a>

<a id="9934" class="Comment">-- EXERCISE 3</a>
<a id="_||_"></a><a id="9948" href="Chapter.Intro.Bool.html#9948" class="Function Operator">_||_</a> <a id="9953" class="Symbol">:</a> <a id="9955" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="9960" class="Symbol">-&gt;</a> <a id="9963" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="9968" class="Symbol">-&gt;</a> <a id="9971" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="9976" href="Chapter.Intro.Bool.html#9948" class="Function Operator">_||_</a> <a id="9981" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="9987" class="Symbol">_</a> <a id="9989" class="Symbol">=</a> <a id="9991" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>
<a id="9996" href="Chapter.Intro.Bool.html#9948" class="Function Operator">_||_</a> <a id="10001" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10007" href="Chapter.Intro.Bool.html#10007" class="Bound">y</a> <a id="10009" class="Symbol">=</a> <a id="10011" href="Chapter.Intro.Bool.html#10007" class="Bound">y</a>

<a id="10014" class="Comment">-- EXERCISE 4</a>
<a id="10028" class="Keyword">infixl</a> <a id="10035" class="Number">5</a> <a id="10037" href="Chapter.Intro.Bool.html#9948" class="Function Operator">_||_</a>

<a id="10043" class="Comment">-- the value of false &amp;&amp; true || true can be either true or false</a>
<a id="10109" class="Comment">-- depending on the priority given to &amp;&amp; and ||. If &amp;&amp; has greater</a>
<a id="10176" class="Comment">-- priority than ||, we have</a>
<a id="10205" class="Comment">--</a>
<a id="10208" class="Comment">--   false &amp;&amp; true || true = (false &amp;&amp; true) || true</a>
<a id="10261" class="Comment">--                         = false || true</a>
<a id="10304" class="Comment">--                         = true</a>
<a id="10338" class="Comment">--</a>
<a id="10341" class="Comment">-- Conversely, if || has greater priority than &amp;&amp;, we have</a>
<a id="10400" class="Comment">--</a>
<a id="10403" class="Comment">--   false &amp;&amp; true || true = false &amp;&amp; (true || true)</a>
<a id="10456" class="Comment">--                         = false &amp;&amp; true</a>
<a id="10499" class="Comment">--                         = false</a>

<a id="10535" class="Comment">-- EXERCISE 5</a>
<a id="xor"></a><a id="10549" href="Chapter.Intro.Bool.html#10549" class="Function">xor</a> <a id="10553" class="Symbol">:</a> <a id="10555" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="10560" class="Symbol">-&gt;</a> <a id="10563" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a> <a id="10568" class="Symbol">-&gt;</a> <a id="10571" href="Chapter.Intro.Bool.html#356" class="Datatype">Bool</a>
<a id="10576" href="Chapter.Intro.Bool.html#10549" class="Function">xor</a> <a id="10580" href="Chapter.Intro.Bool.html#375" class="InductiveConstructor">true</a>  <a id="10586" href="Chapter.Intro.Bool.html#10586" class="Bound">y</a> <a id="10588" class="Symbol">=</a> <a id="10590" href="Chapter.Intro.Bool.html#1960" class="Function">not</a> <a id="10594" href="Chapter.Intro.Bool.html#10586" class="Bound">y</a>
<a id="10596" href="Chapter.Intro.Bool.html#10549" class="Function">xor</a> <a id="10600" href="Chapter.Intro.Bool.html#390" class="InductiveConstructor">false</a> <a id="10606" href="Chapter.Intro.Bool.html#10606" class="Bound">y</a> <a id="10608" class="Symbol">=</a> <a id="10610" href="Chapter.Intro.Bool.html#10606" class="Bound">y</a>
</pre>{:.solution}
