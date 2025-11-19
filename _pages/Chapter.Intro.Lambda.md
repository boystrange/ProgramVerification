---
title: Types and functions
next:  Chapter.Intro.Bool
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Intro.Lambda.html" class="Module">Chapter.Intro.Lambda</a> <a id="95" class="Keyword">where</a>
</pre>
## Imports

To try out the examples discussed in this chapter and to solve the
proposed exercises it is necessary to import the `Nat` module, which
defines the natural numbers and some basic operations on them. We
will see how natural numbers are defined in a [dedicated
chapter](Chapter.Intro.NaturalNumbers.html). For the time being, we
simply import the module and make its content accessible by means of
the following clause.

<pre class="Agda"><a id="541" class="Keyword">open</a> <a id="546" class="Keyword">import</a> <a id="553" href="Library.Nat.html" class="Module">Library.Nat</a>
</pre>
## Simple types

Agda is a strongly typed programming language and every term of the
language must be **well typed** in order to be considered by
Agda. For now we only consider a small set of **simple types**:

* `ℕ` stands for the type of **natural numbers**;
* if `A` and `B` are types, then `(A -> B)` is the type of
  **functions** that, when applied to an argument of type `A`, yield a
  result of type `B`.

To limit the amount of parentheses we have to write in types and to
improve readability, we adopt the following conventions:

* we omit topmost parentheses, so that `A -> B` stands for `(A -> B)`;
* we assume that `->` associates to the **right**, so that e.g. `A
  -> B -> C` stands for `A -> (B -> C)` and not for `(A -> B) -> C`.

## Defining functions

An Agda function is written as a term of the form `λ (x : A) -> M`
where

* `x` is the **name of the argument** of the function;
* `A` is the **type of the argument** of the function;
* `M` is the **body** of the function, namely the expression that
  computes the result of applying the function to its argument.

Below are a few simple examples of functions that make use of types
and operators defined in the `Nat` module:

* `λ (x : ℕ) -> x` is the identity function for natural numbers;
* `λ (x : ℕ) -> x + 1` is the successor function for natural numbers;
* `λ (x : ℕ) -> x ^ 2 + 1` is the function that, applied to a
  natural number $x$, computes $x^2 + 1$.

All of these functions have type `ℕ -> ℕ` since they accept a
natural number as argument (the `ℕ` to the lhs of `->`) and produce
a natural number as result (the `ℕ` to the rhs of `->`).  The type
annotation of the argument can be omitted when its type can be
inferred from the context. For example, since the `+` and `^`
operators defined in the `Nat` module can only be applied to natural
numbers, the last two functions above can be more concisely written
as `λ x -> x + 1` and `λ x -> x ^ 2 + 1` respectively. We can verify
this by asking Agda to compute the type of these functions. This is
achieved by typing `C-c C-d` followed by the function (more
generally the term) for which we want Agda to infer the type.

All the examples above define **anonymous functions**, functions
without a name that are defined "on the spot", wherever we need. It
if often convenient to give names to functions, especially if we
plan to apply them multiple times or if we want to make them
available in a library or a complex Agda development. In an Agda
**program** we can use **definitions** to give names to terms and to
specify their type. For example, the program containing the
following two lines specify that `f` is a function of type `ℕ -> ℕ`
that maps $x$ to $x^2 + 1$:

<pre class="Agda"><a id="f"></a><a id="3281" href="Chapter.Intro.Lambda.html#3281" class="Function">f</a> <a id="3283" class="Symbol">:</a> <a id="3285" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="3287" class="Symbol">-&gt;</a> <a id="3290" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="3292" href="Chapter.Intro.Lambda.html#3281" class="Function">f</a> <a id="3294" class="Symbol">=</a> <a id="3296" class="Symbol">λ</a> <a id="3298" href="Chapter.Intro.Lambda.html#3298" class="Bound">x</a> <a id="3300" class="Symbol">-&gt;</a> <a id="3303" href="Chapter.Intro.Lambda.html#3298" class="Bound">x</a> <a id="3305" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="3307" class="Number">2</a> <a id="3309" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="3311" class="Number">1</a>
</pre>
The first line provides the **signature** of `f`. Top-level
definitions like this one must always be accompanied by a
signature. The second line provides the **definition** of `f` with
which we establish that the name `f` is **definitionally** the same
as the abstraction `λ x -> x ^ 2 + 1`. That is, for Agda the name
`f` and the term `λ x -> x ^ 2 + 1` are **equal**. Note that we omit
the type of the argument `x` for this abstraction, since Agda is
able to figure out that `x` has type `ℕ` from both the signature of
`f` and the fact that the operators `^` and `+` concern natural
numbers. Speaking of these operators, in definitions like this it is
possible to *click* on any colored symbol to reach its definition.

By loading the program using `C-c C-l`, Agda verifies that `f` is
well typed and that its type is consistent with the one provided in
its signature. Once this is done, we can use again `C-c C-d` to
verify that `f` has type `ℕ -> ℕ`.

When defining functions, Agda provides an alternative, more
convenient notation with which argument and body of the function are
separated by the symbol `=` . For example, an equivalent way of
defining `f` is

<pre class="Agda"><a id="f₁"></a><a id="4488" href="Chapter.Intro.Lambda.html#4488" class="Function">f₁</a> <a id="4491" class="Symbol">:</a> <a id="4493" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="4495" class="Symbol">-&gt;</a> <a id="4498" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="4500" href="Chapter.Intro.Lambda.html#4488" class="Function">f₁</a> <a id="4503" href="Chapter.Intro.Lambda.html#4503" class="Bound">x</a> <a id="4505" class="Symbol">=</a> <a id="4507" href="Chapter.Intro.Lambda.html#4503" class="Bound">x</a> <a id="4509" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="4511" class="Number">2</a> <a id="4513" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="4515" class="Number">1</a>
</pre>
which can be read as "`f₁` applied to `x` is equal to `x ^ 2 +
1`". We have named this alternative definition of the function `f₁`
instead of `f` to avoid a *name clash*: there cannot be two
definitions with the same name in the same Agda file. Here and in
the following we will use indices whenever we need to provide
multiple versions of the same definition.

## Applying functions

Applying a function `M` to an argument `N` is achieved simply by
placing `M` and `N` next to each other, usually separated by one
space. For example, the expression `f 2` means the application of
`f` (defined above) to the natural number `2`. We can evaluate this
application by entering `C-c C-n f 2`, with which we obtain `5` as
result. The command `C-c C-n` asks Agda to *evaluate* (technically,
to *normalize*), the provided expression.

Agda is a strongly typed language, in the sense that it only
considers (and evaluates) terms that are **well typed** according to
a specific set of **typing rules**. We will not describe Agda's
typing rules in detail. For the time being, the following informal
statements explain when a function and an application are well
typed:

* If `M` is a term of type `B` under the assumption that `x` has
  type `A`, then `λ (x : A) -> M` is a term of type `A -> B`;
* If `M` is a term of type `A -> B` and `N` is a term of type `A`,
  then `M N` is a term of type `B`.

In order to limit the use of parentheses and improve readability, in
the following we will make extensive use of some (standard)
conventions concerning function definitions and applications:

* We will omit the type of an argument when it is unimportant or
  clear from the context.
* We will often collapse nested functions into one, so that e.g. `λ
  x y z -> M` stands for `λ x -> λ y -> λ z -> M`.
* We will assume that the body of a function extends as much as
  possible to the right. For example, `λ x y -> x y` stands for `λ x
  y -> (x y)` and not for `(λ x y -> x) y`.
* We will assume that application is **left associative**, so that
  `M₁ M₂ M₃` stands for `(M₁ M₂) M₃` and not for `M₁ (M₂ M₃)`.

We will introduce new terms in the following chapters. For the time
being, since we have imported the `Nat` module from the library, a
number of terms defined therein are also available. In particular:

* `zero` of type `ℕ` represents the natural number zero;
* `succ` of type `ℕ -> ℕ` is a function that, applied to a natural
  number, yields its successor.
* `_+_` of type `ℕ -> ℕ -> ℕ` is the function such that `_+_ M N`
  adds `M` and `N`. We often write this application in the usual
  infix notation `M + N`.
* `_^_` of type `ℕ -> ℕ -> ℕ` is the function such that `_^_ M N`
  computes `M` to the power `N`. We often write this application in
  the infix notation `M ^ N`.

The usual positional notation for natural numbers is also available,
so that `0` can be used as abbreviation for `zero`, `2` can be used
for abbreviation for `(succ (succ zero))` and `42` can be used for
abbreviation for 42 applications of `succ` to `zero`.

Finally, a note on **spacing** in Agda: unlike most programming
languages, Agda allows almost any character to be part of an
identifier. For example, `^` and `+` are plain Agda identifiers just
like `f` and `ℕ`. If we write `x^2` (without spaces around `^`),
Agda considers this as a single identifier (for which there is no
definition).

## Multi-argument and higher-order functions

Strictly speaking, all Agda functions have exactly one argument. The
usual way of representing multi-argument functions in a functional
language like Agda is by means of functions that yield other
functions as result. For example, `g` below is defined as a function
that maps $x$ to a function that maps $y$ to $x^2 + 2xy + 1$.

<pre class="Agda"><a id="g"></a><a id="8280" href="Chapter.Intro.Lambda.html#8280" class="Function">g</a> <a id="8282" class="Symbol">:</a> <a id="8284" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8286" class="Symbol">-&gt;</a> <a id="8289" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8291" class="Symbol">-&gt;</a> <a id="8294" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="8296" href="Chapter.Intro.Lambda.html#8280" class="Function">g</a> <a id="8298" class="Symbol">=</a> <a id="8300" class="Symbol">λ</a> <a id="8302" href="Chapter.Intro.Lambda.html#8302" class="Bound">x</a> <a id="8304" class="Symbol">-&gt;</a> <a id="8307" class="Symbol">λ</a> <a id="8309" href="Chapter.Intro.Lambda.html#8309" class="Bound">y</a> <a id="8311" class="Symbol">-&gt;</a> <a id="8314" href="Chapter.Intro.Lambda.html#8302" class="Bound">x</a> <a id="8316" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="8318" class="Number">2</a> <a id="8320" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="8322" class="Number">2</a> <a id="8324" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="8326" href="Chapter.Intro.Lambda.html#8302" class="Bound">x</a> <a id="8328" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="8330" href="Chapter.Intro.Lambda.html#8309" class="Bound">y</a> <a id="8332" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="8334" class="Number">1</a>
</pre>
Equivalently, `g` can be written as follows:

<pre class="Agda"><a id="g₁"></a><a id="8391" href="Chapter.Intro.Lambda.html#8391" class="Function">g₁</a> <a id="8394" class="Symbol">:</a> <a id="8396" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8398" class="Symbol">-&gt;</a> <a id="8401" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8403" class="Symbol">-&gt;</a> <a id="8406" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="8408" href="Chapter.Intro.Lambda.html#8391" class="Function">g₁</a> <a id="8411" href="Chapter.Intro.Lambda.html#8411" class="Bound">x</a> <a id="8413" href="Chapter.Intro.Lambda.html#8413" class="Bound">y</a> <a id="8415" class="Symbol">=</a> <a id="8417" href="Chapter.Intro.Lambda.html#8411" class="Bound">x</a> <a id="8419" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="8421" class="Number">2</a> <a id="8423" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="8425" class="Number">2</a> <a id="8427" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="8429" href="Chapter.Intro.Lambda.html#8411" class="Bound">x</a> <a id="8431" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="8433" href="Chapter.Intro.Lambda.html#8413" class="Bound">y</a> <a id="8435" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="8437" class="Number">1</a>
</pre>
We can use `C-c C-n` to verify that `g 2 3` evaluates to `17`. Since
function application is left associative, `g 2 3` is the same as `(g
2) 3`. That is, we first apply `g` to `2` to obtain the function

    λ y -> 2 ^ 2 + 2 * 2 * y + 1

and then we apply this function to `3`, to obtain
`2 ^ 2 + 2 * 2 * 3 + 1` that is `17`.

As in most functional programming languages, functions are
first-class entities that can be provided as arguments and returned
as results of other functions. For example, the function

<pre class="Agda"><a id="twice"></a><a id="8960" href="Chapter.Intro.Lambda.html#8960" class="Function">twice</a> <a id="8966" class="Symbol">:</a> <a id="8968" class="Symbol">(</a><a id="8969" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8971" class="Symbol">-&gt;</a> <a id="8974" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="8975" class="Symbol">)</a> <a id="8977" class="Symbol">-&gt;</a> <a id="8980" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="8982" class="Symbol">-&gt;</a> <a id="8985" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="8987" href="Chapter.Intro.Lambda.html#8960" class="Function">twice</a> <a id="8993" href="Chapter.Intro.Lambda.html#8993" class="Bound">f</a> <a id="8995" href="Chapter.Intro.Lambda.html#8995" class="Bound">x</a> <a id="8997" class="Symbol">=</a> <a id="8999" href="Chapter.Intro.Lambda.html#8993" class="Bound">f</a> <a id="9001" class="Symbol">(</a><a id="9002" href="Chapter.Intro.Lambda.html#8993" class="Bound">f</a> <a id="9004" href="Chapter.Intro.Lambda.html#8995" class="Bound">x</a><a id="9005" class="Symbol">)</a>
</pre>
applied to a function `f` and an argument `x` applies `f` to `x`
twice. Evaluating `twice f 2` where `f` is the function defined
above yields `26`.

## Exercises

1. Define at least six different versions of the function that
   computes the successor of a natural number.
2. Define a function `poly₁` that, applied to a natural number $x$,
   yields $2x^2$.
3. Define a function `poly₂` that, applied to two natural numbers
   $x$ and $y$, yields $2(x^3 + y^2)$.
4. Which of the following terms are well typed? Use Agda to verify
   whether your answers are correct.
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ -> ℕ) -> x y`
   * `λ (x : (ℕ -> ℕ) -> ℕ) (y : ℕ) -> x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x x y`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x (x y)`
   * `λ (x : ℕ -> ℕ -> ℕ) (y : ℕ) -> x y y`

<pre class="Agda"><a id="9810" class="Comment">-- EXERCISE 1</a>

<a id="succ₁"></a><a id="9825" href="Chapter.Intro.Lambda.html#9825" class="Function">succ₁</a> <a id="9831" class="Symbol">:</a> <a id="9833" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="9835" class="Symbol">-&gt;</a> <a id="9838" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="9840" href="Chapter.Intro.Lambda.html#9825" class="Function">succ₁</a> <a id="9846" class="Symbol">=</a> <a id="9848" href="Library.Nat.html#59" class="InductiveConstructor">succ</a>

<a id="succ₂"></a><a id="9854" href="Chapter.Intro.Lambda.html#9854" class="Function">succ₂</a> <a id="9860" class="Symbol">:</a> <a id="9862" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="9864" class="Symbol">-&gt;</a> <a id="9867" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="9869" href="Chapter.Intro.Lambda.html#9854" class="Function">succ₂</a> <a id="9875" href="Chapter.Intro.Lambda.html#9875" class="Bound">x</a> <a id="9877" class="Symbol">=</a> <a id="9879" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="9884" href="Chapter.Intro.Lambda.html#9875" class="Bound">x</a>

<a id="succ₃"></a><a id="9887" href="Chapter.Intro.Lambda.html#9887" class="Function">succ₃</a> <a id="9893" class="Symbol">:</a> <a id="9895" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="9897" class="Symbol">-&gt;</a> <a id="9900" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="9902" href="Chapter.Intro.Lambda.html#9887" class="Function">succ₃</a> <a id="9908" class="Symbol">=</a> <a id="9910" class="Symbol">λ</a> <a id="9912" href="Chapter.Intro.Lambda.html#9912" class="Bound">x</a> <a id="9914" class="Symbol">-&gt;</a> <a id="9917" href="Chapter.Intro.Lambda.html#9912" class="Bound">x</a> <a id="9919" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="9921" class="Number">1</a>

<a id="succ₄"></a><a id="9924" href="Chapter.Intro.Lambda.html#9924" class="Function">succ₄</a> <a id="9930" class="Symbol">:</a> <a id="9932" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="9934" class="Symbol">-&gt;</a> <a id="9937" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="9939" href="Chapter.Intro.Lambda.html#9924" class="Function">succ₄</a> <a id="9945" class="Symbol">=</a> <a id="9947" class="Symbol">λ</a> <a id="9949" href="Chapter.Intro.Lambda.html#9949" class="Bound">x</a> <a id="9951" class="Symbol">-&gt;</a> <a id="9954" class="Number">1</a> <a id="9956" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="9958" href="Chapter.Intro.Lambda.html#9949" class="Bound">x</a>

<a id="succ₅"></a><a id="9961" href="Chapter.Intro.Lambda.html#9961" class="Function">succ₅</a> <a id="9967" class="Symbol">:</a> <a id="9969" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="9971" class="Symbol">-&gt;</a> <a id="9974" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="9976" href="Chapter.Intro.Lambda.html#9961" class="Function">succ₅</a> <a id="9982" href="Chapter.Intro.Lambda.html#9982" class="Bound">x</a> <a id="9984" class="Symbol">=</a> <a id="9986" href="Chapter.Intro.Lambda.html#9982" class="Bound">x</a> <a id="9988" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="9990" class="Number">1</a>

<a id="succ₆"></a><a id="9993" href="Chapter.Intro.Lambda.html#9993" class="Function">succ₆</a> <a id="9999" class="Symbol">:</a> <a id="10001" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="10003" class="Symbol">-&gt;</a> <a id="10006" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="10008" href="Chapter.Intro.Lambda.html#9993" class="Function">succ₆</a> <a id="10014" href="Chapter.Intro.Lambda.html#10014" class="Bound">x</a> <a id="10016" class="Symbol">=</a> <a id="10018" class="Number">1</a> <a id="10020" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="10022" href="Chapter.Intro.Lambda.html#10014" class="Bound">x</a>

<a id="10025" class="Comment">-- EXERCISE 2</a>

<a id="poly₂"></a><a id="10040" href="Chapter.Intro.Lambda.html#10040" class="Function">poly₂</a> <a id="10046" class="Symbol">:</a> <a id="10048" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="10050" class="Symbol">-&gt;</a> <a id="10053" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="10055" href="Chapter.Intro.Lambda.html#10040" class="Function">poly₂</a> <a id="10061" href="Chapter.Intro.Lambda.html#10061" class="Bound">x</a> <a id="10063" class="Symbol">=</a> <a id="10065" class="Number">2</a> <a id="10067" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="10069" href="Chapter.Intro.Lambda.html#10061" class="Bound">x</a> <a id="10071" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="10073" class="Number">2</a>

<a id="poly₃"></a><a id="10076" href="Chapter.Intro.Lambda.html#10076" class="Function">poly₃</a> <a id="10082" class="Symbol">:</a> <a id="10084" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="10086" class="Symbol">-&gt;</a> <a id="10089" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="10091" class="Symbol">-&gt;</a> <a id="10094" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="10096" href="Chapter.Intro.Lambda.html#10076" class="Function">poly₃</a> <a id="10102" href="Chapter.Intro.Lambda.html#10102" class="Bound">x</a> <a id="10104" href="Chapter.Intro.Lambda.html#10104" class="Bound">y</a> <a id="10106" class="Symbol">=</a> <a id="10108" class="Number">2</a> <a id="10110" href="Library.Nat.html#293" class="Function Operator">*</a> <a id="10112" class="Symbol">(</a><a id="10113" href="Chapter.Intro.Lambda.html#10102" class="Bound">x</a> <a id="10115" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="10117" class="Number">3</a> <a id="10119" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="10121" href="Chapter.Intro.Lambda.html#10104" class="Bound">y</a> <a id="10123" href="Library.Nat.html#352" class="Function Operator">^</a> <a id="10125" class="Number">2</a><a id="10126" class="Symbol">)</a>
</pre>{:.solution}
