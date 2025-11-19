---
title: A taste of Agda
next:  Chapter.Preamble.Setup
---

<pre class="Agda"><a id="67" class="Keyword">module</a> <a id="74" href="Chapter.Preamble.Demo.html" class="Module">Chapter.Preamble.Demo</a> <a id="96" class="Keyword">where</a>
</pre>
## Imports

The program described in this chapter makes use of natural numbers
and of the equality predicate, which must be suitably defined and
imported for this program to correctly type check and compile. The
directives shown below import the necessary definitions from the
Agda library used in this course. For the time being, we will use
natural numbers and equality as black boxes; we will see how they can
be defined in Agda later on.

<pre class="Agda"><a id="554" class="Keyword">open</a> <a id="559" class="Keyword">import</a> <a id="566" href="Library.Equality.html" class="Module">Library.Equality</a>
<a id="583" class="Keyword">open</a> <a id="588" class="Keyword">import</a> <a id="595" href="Library.Equality.Reasoning.html" class="Module">Library.Equality.Reasoning</a>
<a id="622" class="Keyword">open</a> <a id="627" class="Keyword">import</a> <a id="634" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="646" class="Keyword">open</a> <a id="651" class="Keyword">import</a> <a id="658" href="Library.Nat.Properties.html" class="Module">Library.Nat.Properties</a>
</pre>
## The sequence of Fibonacci numbers

To get a taste of Agda, let us write a `fibo` function that computes
the k-th number in the sequence of Fibonacci, that is the sequence

    0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...

that starts with 0 followed by 1 and such that each subsequent
number is the sum of the previous two. For example, we expect `fibo`
to return 55 when it is applied to 10, since 55 is the 11th number
in the sequence. The easiest implementation of `fibo` in Agda is
shown below.

<pre class="Agda"><a id="fibo"></a><a id="1193" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1198" class="Symbol">:</a> <a id="1200" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1202" class="Symbol">-&gt;</a> <a id="1205" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="1207" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1212" class="Number">0</a>               <a id="1228" class="Symbol">=</a> <a id="1230" class="Number">0</a>
<a id="1232" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1237" class="Number">1</a>               <a id="1253" class="Symbol">=</a> <a id="1255" class="Number">1</a>
<a id="1257" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1262" class="Symbol">(</a><a id="1263" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1268" class="Symbol">(</a><a id="1269" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1274" href="Chapter.Preamble.Demo.html#1274" class="Bound">k</a><a id="1275" class="Symbol">))</a> <a id="1278" class="Symbol">=</a> <a id="1280" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1285" href="Chapter.Preamble.Demo.html#1274" class="Bound">k</a> <a id="1287" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="1289" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="1294" class="Symbol">(</a><a id="1295" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1300" href="Chapter.Preamble.Demo.html#1274" class="Bound">k</a><a id="1301" class="Symbol">)</a>
</pre>
Once this script is loaded, we can ask Agda to compute the result of
applying `fibo` to some numbers. By pressing `C-c C-n` and then
entering `fibo 10` we obtain 55, as expected. 

It is a known fact that the shown implementation of `fibo` is very
inefficient. In fact, the time for computing the k-th Fibonacci
number is exponential in k. We can propose a more efficient,
albeit slightly more complex function that computes the k-th
Fibonacci number in linear time, as follows.

<pre class="Agda"><a id="fibo-from"></a><a id="1792" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="1802" class="Symbol">:</a> <a id="1804" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1806" class="Symbol">-&gt;</a> <a id="1809" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1811" class="Symbol">-&gt;</a> <a id="1814" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1816" class="Symbol">-&gt;</a> <a id="1819" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="1821" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="1831" href="Chapter.Preamble.Demo.html#1831" class="Bound">m</a> <a id="1833" href="Chapter.Preamble.Demo.html#1833" class="Bound">n</a> <a id="1835" class="Number">0</a>        <a id="1844" class="Symbol">=</a> <a id="1846" href="Chapter.Preamble.Demo.html#1831" class="Bound">m</a>
<a id="1848" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="1858" href="Chapter.Preamble.Demo.html#1858" class="Bound">m</a> <a id="1860" href="Chapter.Preamble.Demo.html#1860" class="Bound">n</a> <a id="1862" class="Symbol">(</a><a id="1863" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="1868" href="Chapter.Preamble.Demo.html#1868" class="Bound">k</a><a id="1869" class="Symbol">)</a> <a id="1871" class="Symbol">=</a> <a id="1873" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="1883" href="Chapter.Preamble.Demo.html#1860" class="Bound">n</a> <a id="1885" class="Symbol">(</a><a id="1886" href="Chapter.Preamble.Demo.html#1858" class="Bound">m</a> <a id="1888" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="1890" href="Chapter.Preamble.Demo.html#1860" class="Bound">n</a><a id="1891" class="Symbol">)</a> <a id="1893" href="Chapter.Preamble.Demo.html#1868" class="Bound">k</a>

<a id="fast-fibo"></a><a id="1896" href="Chapter.Preamble.Demo.html#1896" class="Function">fast-fibo</a> <a id="1906" class="Symbol">:</a> <a id="1908" href="Library.Nat.html#32" class="Datatype">ℕ</a> <a id="1910" class="Symbol">-&gt;</a> <a id="1913" href="Library.Nat.html#32" class="Datatype">ℕ</a>
<a id="1915" href="Chapter.Preamble.Demo.html#1896" class="Function">fast-fibo</a> <a id="1925" class="Symbol">=</a> <a id="1927" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="1937" class="Number">0</a> <a id="1939" class="Number">1</a>
</pre>
The `fast-fibo` function is just a wrapper for the auxiliary
`fibo-from` function, which takes three arguments: `m` and `n`,
which are supposed to be two subsequent numbers in the Fibonacci
sequence, and then an index `k` which represents the number of steps
to make in the sequence, starting from `m` and `n`, in order to
reach the desired number. When `k` is 0, the desired number is just
`m`. When `k` is greater than 0 we recursively apply `fibo-from` so
that `m` becomes `n`, `n` becomes the sum of the (old) `m` and of
the (old) `n`, and `k` is decreased by one. That is, `fibo-from` is
basically a functional implementation of the classical loop that
finds the desired number in the Fibonacci sequence by using (and
updating) two auxiliary variables `m` and `n` initialized with 0 and
1.

Now, since `fast-fibo` (and particularly `fibo-from` on which it
relies) is substantially more complex than `fibo`, we may wonder
whether `fast-fibo` is in fact equivalent to `fibo`. We may perform
a few tests asking Agda to evaluate `fast-fibo`, but these tests are
**necessarily finite**. The only way to be absolutely sure that
`fibo` and `fast-fibo` are the same function is by **proving** that
they are equivalent.

It is not too difficult to come up with a pen-and-paper proof that
`fibo` and `fast-fibo` are indeed equivalent, but the doubt might
remain that the proof could contain a mistake. After all, we're
humans and all humans make mistakes. Here is where Agda comes to the
rescue, in that it provides us with some tools for **checking**
whether an equivance proof for `fibo` and `fast-fibo` is valid. Even
more surprisingly, the equivalence proof turns out to be a
collection of functions written in the same language in which we
have implemented `fibo` and `fast-fibo`.

Below are two functions, called `lemma` and `theorem`, that prove
the equivalence of `fibo` and `fast-fibo`. For the time being they
look like almost random sequences of meaningless symbols. In this
course we will learn how to write such proofs with the help of the
interactive features of Agda. For the sake of this quick
introduction, though, it may be worth to notice that in the
**types** of these functions we recognize occurrences of `∀` (the
*universal quantifier*), `->` (*logical implication*), and `==`
(*propositional equality*). In particular the type of `theorem`
specifies that, for every natural number `k`, the value resulting
from the application `fast-fibo k` is the same value resulting from
the application `fibo k`.

<pre class="Agda"><a id="lemma"></a><a id="4470" href="Chapter.Preamble.Demo.html#4470" class="Function">lemma</a> <a id="4476" class="Symbol">:</a> <a id="4478" class="Symbol">∀(</a><a id="4480" href="Chapter.Preamble.Demo.html#4480" class="Bound">k</a> <a id="4482" href="Chapter.Preamble.Demo.html#4482" class="Bound">i</a> <a id="4484" class="Symbol">:</a> <a id="4486" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="4487" class="Symbol">)</a> <a id="4489" class="Symbol">-&gt;</a> <a id="4492" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="4502" class="Symbol">(</a><a id="4503" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4508" href="Chapter.Preamble.Demo.html#4480" class="Bound">k</a><a id="4509" class="Symbol">)</a> <a id="4511" class="Symbol">(</a><a id="4512" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4517" class="Symbol">(</a><a id="4518" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4523" href="Chapter.Preamble.Demo.html#4480" class="Bound">k</a><a id="4524" class="Symbol">))</a> <a id="4527" href="Chapter.Preamble.Demo.html#4482" class="Bound">i</a> <a id="4529" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="4532" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4537" class="Symbol">(</a><a id="4538" href="Chapter.Preamble.Demo.html#4482" class="Bound">i</a> <a id="4540" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="4542" href="Chapter.Preamble.Demo.html#4480" class="Bound">k</a><a id="4543" class="Symbol">)</a>
<a id="4545" href="Chapter.Preamble.Demo.html#4470" class="Function">lemma</a> <a id="4551" href="Chapter.Preamble.Demo.html#4551" class="Bound">k</a> <a id="4553" href="Library.Nat.html#48" class="InductiveConstructor">zero</a> <a id="4558" class="Symbol">=</a> <a id="4560" href="Library.Equality.html#125" class="InductiveConstructor">refl</a>
<a id="4565" href="Chapter.Preamble.Demo.html#4470" class="Function">lemma</a> <a id="4571" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a> <a id="4573" class="Symbol">(</a><a id="4574" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4579" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a><a id="4580" class="Symbol">)</a> <a id="4582" class="Symbol">=</a>
  <a id="4586" href="Library.Equality.Reasoning.html#142" class="Function Operator">begin</a>
    <a id="4596" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="4606" class="Symbol">(</a><a id="4607" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4612" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4613" class="Symbol">)</a> <a id="4615" class="Symbol">(</a><a id="4616" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4621" class="Symbol">(</a><a id="4622" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4627" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4628" class="Symbol">))</a> <a id="4631" class="Symbol">(</a><a id="4632" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4637" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a><a id="4638" class="Symbol">)</a> <a id="4640" href="Library.Equality.Reasoning.html#440" class="Function Operator">==⟨⟩</a>
    <a id="4649" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="4659" class="Symbol">(</a><a id="4660" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4665" class="Symbol">(</a><a id="4666" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4671" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4672" class="Symbol">))</a> <a id="4675" class="Symbol">(</a><a id="4676" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4681" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a> <a id="4683" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="4685" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4690" class="Symbol">(</a><a id="4691" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4696" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4697" class="Symbol">))</a> <a id="4700" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a> <a id="4702" href="Library.Equality.Reasoning.html#440" class="Function Operator">==⟨⟩</a>
    <a id="4711" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="4721" class="Symbol">(</a><a id="4722" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4727" class="Symbol">(</a><a id="4728" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4733" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4734" class="Symbol">))</a> <a id="4737" class="Symbol">(</a><a id="4738" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4743" class="Symbol">(</a><a id="4744" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4749" class="Symbol">(</a><a id="4750" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4755" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4756" class="Symbol">)))</a> <a id="4760" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a>
      <a id="4768" href="Library.Equality.Reasoning.html#255" class="Function Operator">==⟨</a> <a id="4772" href="Chapter.Preamble.Demo.html#4470" class="Function">lemma</a> <a id="4778" class="Symbol">(</a><a id="4779" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4784" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4785" class="Symbol">)</a> <a id="4787" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a> <a id="4789" href="Library.Equality.Reasoning.html#255" class="Function Operator">⟩</a>
    <a id="4795" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4800" class="Symbol">(</a><a id="4801" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a> <a id="4803" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="4805" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4810" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4811" class="Symbol">)</a>
      <a id="4819" href="Library.Equality.Reasoning.html#255" class="Function Operator">==⟨</a> <a id="4823" href="Library.Equality.html#373" class="Function">cong</a> <a id="4828" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4833" class="Symbol">(</a><a id="4834" href="Library.Equality.html#226" class="Function">symm</a> <a id="4839" class="Symbol">(</a><a id="4840" href="Library.Nat.Properties.html#370" class="Function">+-succ</a> <a id="4847" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a> <a id="4849" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4850" class="Symbol">))</a> <a id="4853" href="Library.Equality.Reasoning.html#255" class="Function Operator">⟩</a>
    <a id="4859" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4864" class="Symbol">(</a><a id="4865" href="Library.Nat.html#59" class="InductiveConstructor">succ</a> <a id="4870" href="Chapter.Preamble.Demo.html#4579" class="Bound">i</a> <a id="4872" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="4874" href="Chapter.Preamble.Demo.html#4571" class="Bound">k</a><a id="4875" class="Symbol">)</a>
  <a id="4879" href="Library.Equality.Reasoning.html#205" class="Function Operator">end</a>

<a id="theorem"></a><a id="4884" href="Chapter.Preamble.Demo.html#4884" class="Function">theorem</a> <a id="4892" class="Symbol">:</a> <a id="4894" class="Symbol">∀(</a><a id="4896" href="Chapter.Preamble.Demo.html#4896" class="Bound">k</a> <a id="4898" class="Symbol">:</a> <a id="4900" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="4901" class="Symbol">)</a> <a id="4903" class="Symbol">-&gt;</a> <a id="4906" href="Chapter.Preamble.Demo.html#1896" class="Function">fast-fibo</a> <a id="4916" href="Chapter.Preamble.Demo.html#4896" class="Bound">k</a> <a id="4918" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="4921" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="4926" href="Chapter.Preamble.Demo.html#4896" class="Bound">k</a>
<a id="4928" href="Chapter.Preamble.Demo.html#4884" class="Function">theorem</a> <a id="4936" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a> <a id="4938" class="Symbol">=</a>
  <a id="4942" href="Library.Equality.Reasoning.html#142" class="Function Operator">begin</a>
    <a id="4952" href="Chapter.Preamble.Demo.html#1896" class="Function">fast-fibo</a> <a id="4962" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a>     <a id="4968" href="Library.Equality.Reasoning.html#440" class="Function Operator">==⟨⟩</a>
    <a id="4977" href="Chapter.Preamble.Demo.html#1792" class="Function">fibo-from</a> <a id="4987" class="Number">0</a> <a id="4989" class="Number">1</a> <a id="4991" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a> <a id="4993" href="Library.Equality.Reasoning.html#255" class="Function Operator">==⟨</a> <a id="4997" href="Chapter.Preamble.Demo.html#4470" class="Function">lemma</a> <a id="5003" class="Number">0</a> <a id="5005" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a> <a id="5007" href="Library.Equality.Reasoning.html#255" class="Function Operator">⟩</a>
    <a id="5013" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="5018" class="Symbol">(</a><a id="5019" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a> <a id="5021" href="Library.Nat.html#145" class="Function Operator">+</a> <a id="5023" class="Number">0</a><a id="5024" class="Symbol">)</a>    <a id="5029" href="Library.Equality.Reasoning.html#255" class="Function Operator">==⟨</a> <a id="5033" href="Library.Equality.html#373" class="Function">cong</a> <a id="5038" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="5043" class="Symbol">(</a><a id="5044" href="Library.Nat.Properties.html#536" class="Function">+-unit-r</a> <a id="5053" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a><a id="5054" class="Symbol">)</a> <a id="5056" href="Library.Equality.Reasoning.html#255" class="Function Operator">⟩</a>
    <a id="5062" href="Chapter.Preamble.Demo.html#1193" class="Function">fibo</a> <a id="5067" href="Chapter.Preamble.Demo.html#4936" class="Bound">k</a>
  <a id="5071" href="Library.Equality.Reasoning.html#205" class="Function Operator">end</a>
</pre>
By checking that these functions adhere to the types we've given
them, Agda certifies that `fibo` and `fast-fibo` are equivalent. So,
from now on we can safely use whichever function is more convenient,
preferring `fibo` or `fast-fibo` depending on whether readability or
performance is more important.

## Homework

1. Let $F_i$ be the $i$-th Fibonacci number, defined by the equations

   $$
     F_0 = 0
     \qquad
     F_1 = 1
     \qquad
     F_{i+2} = F_i + F_{i+1}
   $$

   Using pencil and paper, prove that `fibo-from` $F_i$ $F_{i+1}$ $k$
   = $F_{i+k}$ by induction on $k$.

   > By induction on $k$. There are two base cases: when $k = 0$,
   > then `fibo-from` $F_i$ $F_{i+1}$ $0$ = $F_i$ = $F_{i+k}$; In
   > the inductive case we have $k > 0$. By definition of
   > `fibo-from` we have `fibo-from` $F_i$ $F_{i+1}$ $k$ =
   > `fibo-from` $F_{i+1}$ $F_{i+2}$ $(k-1)$. Using the induction
   > hypothesis we conclude `fibo-from` $F_{i+1}$ $F_{i+2}$ $(k-1)$
   > = $F_{i+k}$.
   {:.solution}
