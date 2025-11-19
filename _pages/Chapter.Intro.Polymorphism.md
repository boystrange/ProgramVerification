---
title: Polymorphic functions and implicit arguments
next:  Chapter.Intro.Lists
prev:  Chapter.Intro.NaturalNumbers
---

<pre class="Agda"><a id="129" class="Keyword">module</a> <a id="136" href="Chapter.Intro.Polymorphism.html" class="Module">Chapter.Intro.Polymorphism</a> <a id="163" class="Keyword">where</a>
</pre>
In this chapter we study Agda's support for **polymorphism**, namely
the ability of some functions to be applied to arguments of
different types.

## Imports

<pre class="Agda"><a id="337" class="Keyword">open</a> <a id="342" class="Keyword">import</a> <a id="349" href="Library.Bool.html" class="Module">Library.Bool</a>
<a id="362" class="Keyword">open</a> <a id="367" class="Keyword">import</a> <a id="374" href="Library.Nat.html" class="Module">Library.Nat</a>
</pre>
## Polymorphic functions

The behavior of some functions does not depend on any particular
property of their argument. The simplest example of function with
such property is that of the **identity function**, which always
yields the value of its argument. We may conceive several versions
of the identity function, depending on the type of its argument.

<pre class="Agda"><a id="id₁"></a><a id="750" href="Chapter.Intro.Polymorphism.html#750" class="Function">id₁</a> <a id="754" class="Symbol">:</a> <a id="756" href="Library.Bool.html#33" class="Datatype">Bool</a> <a id="761" class="Symbol">-&gt;</a> <a id="764" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="769" href="Chapter.Intro.Polymorphism.html#750" class="Function">id₁</a> <a id="773" href="Chapter.Intro.Polymorphism.html#773" class="Bound">x</a> <a id="775" class="Symbol">=</a> <a id="777" href="Chapter.Intro.Polymorphism.html#773" class="Bound">x</a>

<a id="id₂"></a><a id="780" href="Chapter.Intro.Polymorphism.html#780" class="Function">id₂</a> <a id="784" class="Symbol">:</a> <a id="786" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="788" class="Symbol">-&gt;</a> <a id="791" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="793" href="Chapter.Intro.Polymorphism.html#780" class="Function">id₂</a> <a id="797" href="Chapter.Intro.Polymorphism.html#797" class="Bound">x</a> <a id="799" class="Symbol">=</a> <a id="801" href="Chapter.Intro.Polymorphism.html#797" class="Bound">x</a>

<a id="id₃"></a><a id="804" href="Chapter.Intro.Polymorphism.html#804" class="Function">id₃</a> <a id="808" class="Symbol">:</a> <a id="810" class="Symbol">(</a><a id="811" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="813" class="Symbol">-&gt;</a> <a id="816" href="Library.Bool.html#33" class="Datatype">Bool</a><a id="820" class="Symbol">)</a> <a id="822" class="Symbol">-&gt;</a> <a id="825" class="Symbol">(</a><a id="826" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="828" class="Symbol">-&gt;</a> <a id="831" href="Library.Bool.html#33" class="Datatype">Bool</a><a id="835" class="Symbol">)</a>
<a id="837" href="Chapter.Intro.Polymorphism.html#804" class="Function">id₃</a> <a id="841" href="Chapter.Intro.Polymorphism.html#841" class="Bound">x</a> <a id="843" class="Symbol">=</a> <a id="845" href="Chapter.Intro.Polymorphism.html#841" class="Bound">x</a>
</pre>
Depending on the type of the argument, we would use one version or
the other: if we want to apply the identity function to a boolean
value, then we would use `id₁`; if we want to apply the identity
function to a natural number, then we would use `id₂`; and so on and
so forth.

<pre class="Agda"><a id="1134" href="Chapter.Intro.Polymorphism.html#1134" class="Function">_</a> <a id="1136" class="Symbol">:</a> <a id="1138" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="1143" class="Symbol">_</a> <a id="1145" class="Symbol">=</a> <a id="1147" href="Chapter.Intro.Polymorphism.html#750" class="Function">id₁</a> <a id="1151" href="Library.Bool.html#52" class="InductiveConstructor">true</a>

<a id="1157" href="Chapter.Intro.Polymorphism.html#1157" class="Function">_</a> <a id="1159" class="Symbol">:</a> <a id="1161" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="1163" class="Symbol">_</a> <a id="1165" class="Symbol">=</a> <a id="1167" href="Chapter.Intro.Polymorphism.html#780" class="Function">id₂</a> <a id="1171" class="Number">42</a>
</pre>
The definitions `id₁`, `id₂`, ... of the identity function differ in
the type of their argument, but behave in exactly the same
way. Clearly, it would be desirable to define the identity function
once and for all, and make it applicable to arguments of different
types. In Agda this is made possible by the dependent arrow type.

<pre class="Agda"><a id="id₄"></a><a id="1513" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="1517" class="Symbol">:</a> <a id="1519" class="Symbol">∀(</a><a id="1521" href="Chapter.Intro.Polymorphism.html#1521" class="Bound">A</a> <a id="1523" class="Symbol">:</a> <a id="1525" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="1528" class="Symbol">)</a> <a id="1530" class="Symbol">-&gt;</a> <a id="1533" href="Chapter.Intro.Polymorphism.html#1521" class="Bound">A</a> <a id="1535" class="Symbol">-&gt;</a> <a id="1538" href="Chapter.Intro.Polymorphism.html#1521" class="Bound">A</a>
<a id="1540" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="1544" href="Chapter.Intro.Polymorphism.html#1544" class="Bound">A</a> <a id="1546" href="Chapter.Intro.Polymorphism.html#1546" class="Bound">x</a> <a id="1548" class="Symbol">=</a> <a id="1550" href="Chapter.Intro.Polymorphism.html#1546" class="Bound">x</a>
</pre>
Note that the domain of `id₄` is some `Set` `A` (that is, `A` is a
type in Agda's terminology) and the codomain of `id₄` is the type `A
-> A`. Basically, we have turned the one-argument, monomorphic
identity function into a two-arguments, polymorphic identity
function where the first argument is the type of the second
argument. We can now use `id₄` in different places with different
argument types.

<pre class="Agda"><a id="1964" href="Chapter.Intro.Polymorphism.html#1964" class="Function">_</a> <a id="1966" class="Symbol">:</a> <a id="1968" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="1973" class="Symbol">_</a> <a id="1975" class="Symbol">=</a> <a id="1977" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="1981" href="Library.Bool.html#33" class="Datatype">Bool</a> <a id="1986" href="Library.Bool.html#52" class="InductiveConstructor">true</a>

<a id="1992" href="Chapter.Intro.Polymorphism.html#1992" class="Function">_</a> <a id="1994" class="Symbol">:</a> <a id="1996" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="1998" class="Symbol">_</a> <a id="2000" class="Symbol">=</a> <a id="2002" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="2006" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="2008" class="Number">42</a>
</pre>
## Implicit arguments

You may have noticed that the argument `A` in the definition of
`id₄` plays no role in the definition of `id₄`. In fact, that
argument is somewhat *redundant* since it must coincide with the
type of `x`, the second argument of `id₄`. We can verify this
redundancy in practice by observing that Agda can automatically
*infer* the type of the first argument whenever we provide the
second one.

<pre class="Agda"><a id="2436" href="Chapter.Intro.Polymorphism.html#2436" class="Function">_</a> <a id="2438" class="Symbol">:</a> <a id="2440" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="2445" class="Symbol">_</a> <a id="2447" class="Symbol">=</a> <a id="2449" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="2453" class="Symbol">_</a> <a id="2455" href="Library.Bool.html#52" class="InductiveConstructor">true</a>

<a id="2461" href="Chapter.Intro.Polymorphism.html#2461" class="Function">_</a> <a id="2463" class="Symbol">:</a> <a id="2465" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="2467" class="Symbol">_</a> <a id="2469" class="Symbol">=</a> <a id="2471" href="Chapter.Intro.Polymorphism.html#1513" class="Function">id₄</a> <a id="2475" class="Symbol">_</a> <a id="2477" class="Number">42</a>
</pre>
In these definitions, the underscore `_` stands for an expression
that we ask Agda to automatically infer. Of course, not everything
can be inferred automatically, or else there would be no point in
learning how to program in Agda. In the particular case of `id₄`,
however, the term that is meant to replace the underscore is
uniquely determined by the second argument: since `true` has type
`Bool`, the first underscore must be replaced by `Bool`; since `42`
has type `ℕ`, the second underscore must be replaced by `ℕ`. This
fact makes `id₄` slightly annoying to use, since the programmer is
required to systematically provide an argument that Agda can infer
by itself. In the end, the programmer will typically apply `id₄` to
an underscore followed by the actual argument. We can spare this
burden to the programmer by declaring that the first argument of
`id₄` is **implicit**. As the name suggests, implicit arguments can
be omitted in the program since they are supposed to be inferred
automatically. An implicit argument is declared using braces `{...}`
instead of parentheses `(...)`. So, the final version of the
polymorphic identity function with implicit arguments is the
following.

<pre class="Agda"><a id="id"></a><a id="3683" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="3686" class="Symbol">:</a> <a id="3688" class="Symbol">∀{</a><a id="3690" href="Chapter.Intro.Polymorphism.html#3690" class="Bound">A</a> <a id="3692" class="Symbol">:</a> <a id="3694" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="3697" class="Symbol">}</a> <a id="3699" class="Symbol">-&gt;</a> <a id="3702" href="Chapter.Intro.Polymorphism.html#3690" class="Bound">A</a> <a id="3704" class="Symbol">-&gt;</a> <a id="3707" href="Chapter.Intro.Polymorphism.html#3690" class="Bound">A</a>
<a id="3709" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="3712" href="Chapter.Intro.Polymorphism.html#3712" class="Bound">x</a> <a id="3714" class="Symbol">=</a> <a id="3716" href="Chapter.Intro.Polymorphism.html#3712" class="Bound">x</a>
</pre>
Notice that the implicit argument is also omitted in the very
definition of `id`. Now, we can apply `id` to whatever argument we
like, without explicitly supplying its type.

<pre class="Agda"><a id="3902" href="Chapter.Intro.Polymorphism.html#3902" class="Function">_</a> <a id="3904" class="Symbol">:</a> <a id="3906" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="3911" class="Symbol">_</a> <a id="3913" class="Symbol">=</a> <a id="3915" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="3918" href="Library.Bool.html#52" class="InductiveConstructor">true</a>

<a id="3924" href="Chapter.Intro.Polymorphism.html#3924" class="Function">_</a> <a id="3926" class="Symbol">:</a> <a id="3928" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="3930" class="Symbol">_</a> <a id="3932" class="Symbol">=</a> <a id="3934" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="3937" class="Number">42</a>
</pre>
There are cases in which Agda is not able to automatically infer an
implicit. In these cases, we can supply it explicitly, by placing
the implicit argument within braces.

<pre class="Agda"><a id="4121" href="Chapter.Intro.Polymorphism.html#4121" class="Function">_</a> <a id="4123" class="Symbol">:</a> <a id="4125" href="Library.Bool.html#33" class="Datatype">Bool</a>
<a id="4130" class="Symbol">_</a> <a id="4132" class="Symbol">=</a> <a id="4134" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="4137" class="Symbol">{</a><a id="4138" href="Library.Bool.html#33" class="Datatype">Bool</a><a id="4142" class="Symbol">}</a> <a id="4144" href="Library.Bool.html#52" class="InductiveConstructor">true</a>

<a id="4150" href="Chapter.Intro.Polymorphism.html#4150" class="Function">_</a> <a id="4152" class="Symbol">:</a> <a id="4154" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="4156" class="Symbol">_</a> <a id="4158" class="Symbol">=</a> <a id="4160" href="Chapter.Intro.Polymorphism.html#3683" class="Function">id</a> <a id="4163" class="Symbol">{</a><a id="4164" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="4165" class="Symbol">}</a> <a id="4167" class="Number">42</a>
</pre>
Similarly, we can name the implicit argument when defining the
function, in case it is needed in the body of the function.

<pre class="Agda"><a id="id₅"></a><a id="4303" href="Chapter.Intro.Polymorphism.html#4303" class="Function">id₅</a> <a id="4307" class="Symbol">:</a> <a id="4309" class="Symbol">∀{</a><a id="4311" href="Chapter.Intro.Polymorphism.html#4311" class="Bound">A</a> <a id="4313" class="Symbol">:</a> <a id="4315" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="4318" class="Symbol">}</a> <a id="4320" class="Symbol">-&gt;</a> <a id="4323" href="Chapter.Intro.Polymorphism.html#4311" class="Bound">A</a> <a id="4325" class="Symbol">-&gt;</a> <a id="4328" href="Chapter.Intro.Polymorphism.html#4311" class="Bound">A</a>
<a id="4330" href="Chapter.Intro.Polymorphism.html#4303" class="Function">id₅</a> <a id="4334" class="Symbol">{</a><a id="4335" href="Chapter.Intro.Polymorphism.html#4335" class="Bound">A</a><a id="4336" class="Symbol">}</a> <a id="4338" href="Chapter.Intro.Polymorphism.html#4338" class="Bound">x</a> <a id="4340" class="Symbol">=</a> <a id="4342" href="Chapter.Intro.Polymorphism.html#4338" class="Bound">x</a>
</pre>
There is no general guideline to establish whether an argument
should be explicit or implicit. As a rule of thumb, an argument can
be declared implicit if it also occurs later in the same type. We
will see systematic applications of this rule in the next chapters,
as we make greater use of dependent types.

## Exercises

1. Implement the function `flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C`.
2. Implement the function `_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C`.
3. Provide two syntactically different (but equivalent)
   implementations of the function `apply : ∀{A B : Set} -> (A -> B) -> A -> B`.

<pre class="Agda"><a id="flip"></a><a id="4985" href="Chapter.Intro.Polymorphism.html#4985" class="Function">flip</a> <a id="4990" class="Symbol">:</a> <a id="4992" class="Symbol">∀{</a><a id="4994" href="Chapter.Intro.Polymorphism.html#4994" class="Bound">A</a> <a id="4996" href="Chapter.Intro.Polymorphism.html#4996" class="Bound">B</a> <a id="4998" href="Chapter.Intro.Polymorphism.html#4998" class="Bound">C</a> <a id="5000" class="Symbol">:</a> <a id="5002" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5005" class="Symbol">}</a> <a id="5007" class="Symbol">-&gt;</a> <a id="5010" class="Symbol">(</a><a id="5011" href="Chapter.Intro.Polymorphism.html#4994" class="Bound">A</a> <a id="5013" class="Symbol">-&gt;</a> <a id="5016" href="Chapter.Intro.Polymorphism.html#4996" class="Bound">B</a> <a id="5018" class="Symbol">-&gt;</a> <a id="5021" href="Chapter.Intro.Polymorphism.html#4998" class="Bound">C</a><a id="5022" class="Symbol">)</a> <a id="5024" class="Symbol">-&gt;</a> <a id="5027" href="Chapter.Intro.Polymorphism.html#4996" class="Bound">B</a> <a id="5029" class="Symbol">-&gt;</a> <a id="5032" href="Chapter.Intro.Polymorphism.html#4994" class="Bound">A</a> <a id="5034" class="Symbol">-&gt;</a> <a id="5037" href="Chapter.Intro.Polymorphism.html#4998" class="Bound">C</a>
<a id="5039" href="Chapter.Intro.Polymorphism.html#4985" class="Function">flip</a> <a id="5044" class="Symbol">=</a> <a id="5046" class="Symbol">λ</a> <a id="5048" href="Chapter.Intro.Polymorphism.html#5048" class="Bound">f</a> <a id="5050" href="Chapter.Intro.Polymorphism.html#5050" class="Bound">x</a> <a id="5052" href="Chapter.Intro.Polymorphism.html#5052" class="Bound">y</a> <a id="5054" class="Symbol">-&gt;</a> <a id="5057" href="Chapter.Intro.Polymorphism.html#5048" class="Bound">f</a> <a id="5059" href="Chapter.Intro.Polymorphism.html#5052" class="Bound">y</a> <a id="5061" href="Chapter.Intro.Polymorphism.html#5050" class="Bound">x</a>

<a id="_∘_"></a><a id="5064" href="Chapter.Intro.Polymorphism.html#5064" class="Function Operator">_∘_</a> <a id="5068" class="Symbol">:</a> <a id="5070" class="Symbol">∀{</a><a id="5072" href="Chapter.Intro.Polymorphism.html#5072" class="Bound">A</a> <a id="5074" href="Chapter.Intro.Polymorphism.html#5074" class="Bound">B</a> <a id="5076" href="Chapter.Intro.Polymorphism.html#5076" class="Bound">C</a> <a id="5078" class="Symbol">:</a> <a id="5080" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5083" class="Symbol">}</a> <a id="5085" class="Symbol">-&gt;</a> <a id="5088" class="Symbol">(</a><a id="5089" href="Chapter.Intro.Polymorphism.html#5074" class="Bound">B</a> <a id="5091" class="Symbol">-&gt;</a> <a id="5094" href="Chapter.Intro.Polymorphism.html#5076" class="Bound">C</a><a id="5095" class="Symbol">)</a> <a id="5097" class="Symbol">-&gt;</a> <a id="5100" class="Symbol">(</a><a id="5101" href="Chapter.Intro.Polymorphism.html#5072" class="Bound">A</a> <a id="5103" class="Symbol">-&gt;</a> <a id="5106" href="Chapter.Intro.Polymorphism.html#5074" class="Bound">B</a><a id="5107" class="Symbol">)</a> <a id="5109" class="Symbol">-&gt;</a> <a id="5112" href="Chapter.Intro.Polymorphism.html#5072" class="Bound">A</a> <a id="5114" class="Symbol">-&gt;</a> <a id="5117" href="Chapter.Intro.Polymorphism.html#5076" class="Bound">C</a>
<a id="5119" href="Chapter.Intro.Polymorphism.html#5119" class="Bound">f</a> <a id="5121" href="Chapter.Intro.Polymorphism.html#5064" class="Function Operator">∘</a> <a id="5123" href="Chapter.Intro.Polymorphism.html#5123" class="Bound">g</a> <a id="5125" class="Symbol">=</a> <a id="5127" class="Symbol">λ</a> <a id="5129" href="Chapter.Intro.Polymorphism.html#5129" class="Bound">x</a> <a id="5131" class="Symbol">-&gt;</a> <a id="5134" href="Chapter.Intro.Polymorphism.html#5119" class="Bound">f</a> <a id="5136" class="Symbol">(</a><a id="5137" href="Chapter.Intro.Polymorphism.html#5123" class="Bound">g</a> <a id="5139" href="Chapter.Intro.Polymorphism.html#5129" class="Bound">x</a><a id="5140" class="Symbol">)</a>

<a id="5143" class="Comment">-- the first version of apply follows from the definition of</a>
<a id="5204" class="Comment">-- function application</a>

<a id="apply₁"></a><a id="5229" href="Chapter.Intro.Polymorphism.html#5229" class="Function">apply₁</a> <a id="5236" class="Symbol">:</a> <a id="5238" class="Symbol">∀{</a><a id="5240" href="Chapter.Intro.Polymorphism.html#5240" class="Bound">A</a> <a id="5242" href="Chapter.Intro.Polymorphism.html#5242" class="Bound">B</a> <a id="5244" class="Symbol">:</a> <a id="5246" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5249" class="Symbol">}</a> <a id="5251" class="Symbol">-&gt;</a> <a id="5254" class="Symbol">(</a><a id="5255" href="Chapter.Intro.Polymorphism.html#5240" class="Bound">A</a> <a id="5257" class="Symbol">-&gt;</a> <a id="5260" href="Chapter.Intro.Polymorphism.html#5242" class="Bound">B</a><a id="5261" class="Symbol">)</a> <a id="5263" class="Symbol">-&gt;</a> <a id="5266" href="Chapter.Intro.Polymorphism.html#5240" class="Bound">A</a> <a id="5268" class="Symbol">-&gt;</a> <a id="5271" href="Chapter.Intro.Polymorphism.html#5242" class="Bound">B</a>
<a id="5273" href="Chapter.Intro.Polymorphism.html#5229" class="Function">apply₁</a> <a id="5280" href="Chapter.Intro.Polymorphism.html#5280" class="Bound">f</a> <a id="5282" href="Chapter.Intro.Polymorphism.html#5282" class="Bound">x</a> <a id="5284" class="Symbol">=</a> <a id="5286" href="Chapter.Intro.Polymorphism.html#5280" class="Bound">f</a> <a id="5288" href="Chapter.Intro.Polymorphism.html#5282" class="Bound">x</a>

<a id="5291" class="Comment">-- the second version of apply is just a specialized identity</a>
<a id="5353" class="Comment">-- function</a>

<a id="apply₂"></a><a id="5366" href="Chapter.Intro.Polymorphism.html#5366" class="Function">apply₂</a> <a id="5373" class="Symbol">:</a> <a id="5375" class="Symbol">∀{</a><a id="5377" href="Chapter.Intro.Polymorphism.html#5377" class="Bound">A</a> <a id="5379" href="Chapter.Intro.Polymorphism.html#5379" class="Bound">B</a> <a id="5381" class="Symbol">:</a> <a id="5383" href="Agda.Primitive.html#388" class="Primitive">Set</a><a id="5386" class="Symbol">}</a> <a id="5388" class="Symbol">-&gt;</a> <a id="5391" class="Symbol">(</a><a id="5392" href="Chapter.Intro.Polymorphism.html#5377" class="Bound">A</a> <a id="5394" class="Symbol">-&gt;</a> <a id="5397" href="Chapter.Intro.Polymorphism.html#5379" class="Bound">B</a><a id="5398" class="Symbol">)</a> <a id="5400" class="Symbol">-&gt;</a> <a id="5403" href="Chapter.Intro.Polymorphism.html#5377" class="Bound">A</a> <a id="5405" class="Symbol">-&gt;</a> <a id="5408" href="Chapter.Intro.Polymorphism.html#5379" class="Bound">B</a>
<a id="5410" href="Chapter.Intro.Polymorphism.html#5366" class="Function">apply₂</a> <a id="5417" href="Chapter.Intro.Polymorphism.html#5417" class="Bound">x</a> <a id="5419" class="Symbol">=</a> <a id="5421" href="Chapter.Intro.Polymorphism.html#5417" class="Bound">x</a>
</pre>{:.solution}
