---
title: Intrinsic verification of insertion sort
prev:  Chapter.Fun.ExtrinsicInsertionSort
---

<pre class="Agda"><a id="104" class="Keyword">module</a> <a id="111" href="Chapter.Fun.IntrinsicInsertionSort.html" class="Module">Chapter.Fun.IntrinsicInsertionSort</a> <a id="146" class="Keyword">where</a>
</pre>
The extrinsic verification of insertion sort allowed us to prove the
correctness of insertion sort by considering each aspect of the
algorithm in isolation. Indeed, we have defined the algorithm
(`insertion-sort`), the proof that the algorithm yields a sorted
list (`sorted-insertion-sort`) and the proof that the algorithm
yields a permutation of the original list
(`insertion-sort-permutation`) as separate elements. It is easy to
observe that these elements are structurally related. In particular,
most proofs must perform a case analysis on an application of
`le-total` because that is the way in which the `insert` function is
defined. As a consequence, there is a certain amount of redundancy
in the proofs.

In this chapter we revisit the verification of insertion sort, but
we do so using a different approach called *intrinsic
verification*. In this approach, the implementation of the algorithm
and the proof of its properties are done simultaneously. As we will
see, the overall amount of Agda code we have to write is noticeably
smaller, although the code itself is necessarily more convoluted.

## Imports

<pre class="Agda"><a id="1282" class="Keyword">open</a> <a id="1287" class="Keyword">import</a> <a id="1294" href="Library.Logic.html" class="Module">Library.Logic</a>
<a id="1308" class="Keyword">open</a> <a id="1313" class="Keyword">import</a> <a id="1320" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="1332" class="Keyword">open</a> <a id="1337" class="Keyword">import</a> <a id="1344" href="Library.List.html" class="Module">Library.List</a>
<a id="1357" class="Keyword">open</a> <a id="1362" class="Keyword">import</a> <a id="1369" href="Library.LessThan.html" class="Module">Library.LessThan</a>
<a id="1386" class="Keyword">open</a> <a id="1391" class="Keyword">import</a> <a id="1398" href="Chapter.Fun.SortedLists.html" class="Module">Chapter.Fun.SortedLists</a>
</pre>
## Intrinsically verified insertion

As expected, if we aim at providing an intrinsically verified
insertion sort we have to provide an intrinsically verified
insertion operation, which we specify thus.

<pre class="Agda"><a id="intrinsic-insert"></a><a id="1635" href="Chapter.Fun.IntrinsicInsertionSort.html#1635" class="Function">intrinsic-insert</a> <a id="1652" class="Symbol">:</a> <a id="1654" class="Symbol">∀(</a><a id="1656" href="Chapter.Fun.IntrinsicInsertionSort.html#1656" class="Bound">x</a> <a id="1658" class="Symbol">:</a> <a id="1660" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="1661" class="Symbol">)</a> <a id="1663" class="Symbol">(</a><a id="1664" href="Chapter.Fun.IntrinsicInsertionSort.html#1664" class="Bound">ys</a> <a id="1667" class="Symbol">:</a> <a id="1669" href="Library.List.html#84" class="Datatype">List</a> <a id="1674" href="Library.Nat.html#32" class="Datatype">ℕ</a><a id="1675" class="Symbol">)</a> <a id="1677" class="Symbol">-&gt;</a> <a id="1680" href="Chapter.Fun.SortedLists.html#4486" class="Datatype">Sorted</a> <a id="1687" href="Chapter.Fun.IntrinsicInsertionSort.html#1664" class="Bound">ys</a> <a id="1690" class="Symbol">-&gt;</a>
                   <a id="1712" href="Library.Logic.html#632" class="Function">∃[</a> <a id="1715" href="Chapter.Fun.IntrinsicInsertionSort.html#1715" class="Bound">zs</a> <a id="1718" href="Library.Logic.html#632" class="Function">]</a> <a id="1720" href="Chapter.Fun.IntrinsicInsertionSort.html#1715" class="Bound">zs</a> <a id="1723" href="Chapter.Fun.SortedLists.html#6290" class="Datatype Operator">#</a> <a id="1725" href="Chapter.Fun.IntrinsicInsertionSort.html#1656" class="Bound">x</a> <a id="1727" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="1730" href="Chapter.Fun.IntrinsicInsertionSort.html#1664" class="Bound">ys</a> <a id="1733" href="Library.Logic.html#1349" class="Function Operator">∧</a> <a id="1735" href="Chapter.Fun.SortedLists.html#4486" class="Datatype">Sorted</a> <a id="1742" href="Chapter.Fun.IntrinsicInsertionSort.html#1715" class="Bound">zs</a>
</pre>
In words, the insert operation applied to a number `x` and a sorted
list `ys` yields another sorted list `zs` that is a permutation of
`x :: ys`. Note that now the function takes not only the element and
the list on which it operates, but also a proof that the list is
sorted.

The base case in which `ys` is empty is handled by the following
equation.

<pre class="Agda"><a id="2108" href="Chapter.Fun.IntrinsicInsertionSort.html#1635" class="Function">intrinsic-insert</a> <a id="2125" href="Chapter.Fun.IntrinsicInsertionSort.html#2125" class="Bound">x</a> <a id="2127" href="Library.List.html#113" class="InductiveConstructor">[]</a> <a id="2130" href="Chapter.Fun.SortedLists.html#4517" class="InductiveConstructor">sorted-[]</a> <a id="2140" class="Symbol">=</a> <a id="2142" href="Library.List.html#159" class="Function Operator">[</a> <a id="2144" href="Chapter.Fun.IntrinsicInsertionSort.html#2125" class="Bound">x</a> <a id="2146" href="Library.List.html#159" class="Function Operator">]</a> <a id="2148" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="2150" href="Chapter.Fun.SortedLists.html#6338" class="InductiveConstructor">#refl</a> <a id="2156" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="2158" href="Chapter.Fun.SortedLists.html#4541" class="InductiveConstructor">sorted-::</a> <a id="2168" href="Chapter.Fun.SortedLists.html#3538" class="InductiveConstructor">lb-[]</a> <a id="2174" href="Chapter.Fun.SortedLists.html#4517" class="InductiveConstructor">sorted-[]</a>
</pre>
Remeber that a proof of an existential quantification `∃[ x ] P` is
a pair consisting of a witness and a proof that the witness
satisfies `P`. In this case, the predicate `P` is a conjunction
whose proof is itself a pair. For this reason, `intrinsic-insert`
yields a *triple* made of the witness, which is the singleton list
`[ x ]`, a proof that `[ x ]` is a permutation of `x :: []` and a
proof that `[ x ]` is sorted. Recall from the definition of `[_]`
that `[ x ]` and `x :: []` are definitionally equal, so `#refl`
suffices to prove that they are one the permutation of the other.

When we are inserting `x` in a non-empty list `y :: ys` we have to
establish the relationship between `x` and `y`, which we do by
performing case analysis on `le-total x y`.

<pre class="Agda"><a id="2956" href="Chapter.Fun.IntrinsicInsertionSort.html#1635" class="Function">intrinsic-insert</a> <a id="2973" href="Chapter.Fun.IntrinsicInsertionSort.html#2973" class="Bound">x</a> <a id="2975" class="Symbol">(</a><a id="2976" href="Chapter.Fun.IntrinsicInsertionSort.html#2976" class="Bound">y</a> <a id="2978" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="2981" href="Chapter.Fun.IntrinsicInsertionSort.html#2981" class="Bound">ys</a><a id="2983" class="Symbol">)</a> <a id="2985" class="Symbol">(</a><a id="2986" href="Chapter.Fun.SortedLists.html#4541" class="InductiveConstructor">sorted-::</a> <a id="2996" href="Chapter.Fun.IntrinsicInsertionSort.html#2996" class="Bound">y≤ys</a> <a id="3001" href="Chapter.Fun.IntrinsicInsertionSort.html#3001" class="Bound">ys-sorted</a><a id="3010" class="Symbol">)</a> <a id="3012" class="Keyword">with</a> <a id="3017" href="Library.LessThan.html#770" class="Function">le-total</a> <a id="3026" href="Chapter.Fun.IntrinsicInsertionSort.html#2973" class="Bound">x</a> <a id="3028" href="Chapter.Fun.IntrinsicInsertionSort.html#2976" class="Bound">y</a>
</pre>
Since the list in which we are inserting `x` is not empty, the proof
that it is sorted must have the form `sorted-:: y≤ys ys-sorted`,
which contains a sub-proof that `y` is a lower bound for `ys` and
that `ys` is itself sorted. Let us now consider the case in which `x
<= y`.

<pre class="Agda"><a id="3316" class="Symbol">...</a> <a id="3320" class="Symbol">|</a> <a id="3322" href="Library.Logic.html#1446" class="InductiveConstructor">inl</a> <a id="3326" href="Chapter.Fun.IntrinsicInsertionSort.html#3326" class="Bound">x≤y</a> <a id="3330" class="Symbol">=</a> <a id="3332" class="Bound">x</a> <a id="3334" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="3337" class="Bound">y</a> <a id="3339" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="3342" class="Bound">ys</a> <a id="3345" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
                <a id="3363" href="Chapter.Fun.SortedLists.html#6338" class="InductiveConstructor">#refl</a> <a id="3369" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
                <a id="3387" href="Chapter.Fun.SortedLists.html#4541" class="InductiveConstructor">sorted-::</a> <a id="3397" class="Symbol">(</a><a id="3398" href="Chapter.Fun.SortedLists.html#3564" class="InductiveConstructor">lb-::</a> <a id="3404" href="Chapter.Fun.IntrinsicInsertionSort.html#3326" class="Bound">x≤y</a> <a id="3408" class="Symbol">(</a><a id="3409" href="Chapter.Fun.SortedLists.html#3789" class="Function">lower-lower-bound</a> <a id="3427" href="Chapter.Fun.IntrinsicInsertionSort.html#3326" class="Bound">x≤y</a> <a id="3431" class="Bound">y≤ys</a><a id="3435" class="Symbol">))</a>
                          <a id="3464" class="Symbol">(</a><a id="3465" href="Chapter.Fun.SortedLists.html#4541" class="InductiveConstructor">sorted-::</a> <a id="3475" class="Bound">y≤ys</a> <a id="3480" class="Bound">ys-sorted</a><a id="3489" class="Symbol">)</a>
</pre>
Here `x` is inserted just at the front of the list, so no swapping
is necessary and `#refl` suffices as far as permutations are
concerned. In order to prove that the resulting list is sorted we
need a proof that `x` is a lower bound for `y :: ys`, which we
obtain from the proof that `y` is a lower bound for `ys` along with
the hypothesis `x≤y` using the `lower-lower-bound` lemma that we
have proved in a previous chapter.

<pre class="Agda"><a id="3926" class="Symbol">...</a> <a id="3930" class="Symbol">|</a> <a id="3932" href="Library.Logic.html#1465" class="InductiveConstructor">inr</a> <a id="3936" href="Chapter.Fun.IntrinsicInsertionSort.html#3936" class="Bound">y≤x</a> <a id="3940" class="Keyword">with</a> <a id="3945" href="Chapter.Fun.IntrinsicInsertionSort.html#1635" class="Function">intrinsic-insert</a> <a id="3962" class="Bound">x</a> <a id="3964" class="Bound">ys</a> <a id="3967" class="Bound">ys-sorted</a>
</pre>
If `y <= x`, then we have to insert `x` in `ys`. This operation will
not only return the resulting list `zs`, but also a proof `π` that
`zs` is a permutation of `x :: ys` and a proof `zs-sorted` that `zs`
is sorted. We combine these proofs in the result of the function.

<pre class="Agda"><a id="4258" class="Symbol">...</a> <a id="4262" class="Symbol">|</a> <a id="4264" href="Chapter.Fun.IntrinsicInsertionSort.html#4264" class="Bound">zs</a> <a id="4267" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="4269" href="Chapter.Fun.IntrinsicInsertionSort.html#4269" class="Bound">π</a> <a id="4271" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="4273" href="Chapter.Fun.IntrinsicInsertionSort.html#4273" class="Bound">zs-sorted</a> <a id="4283" class="Symbol">=</a>
  <a id="4287" class="Bound">y</a> <a id="4289" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4292" href="Chapter.Fun.IntrinsicInsertionSort.html#4264" class="Bound">zs</a> <a id="4295" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
  <a id="4299" class="Symbol">(</a><a id="4300" href="Chapter.Fun.SortedLists.html#7256" class="Function Operator">#begin</a>
    <a id="4311" class="Bound">y</a> <a id="4313" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4316" href="Chapter.Fun.IntrinsicInsertionSort.html#4264" class="Bound">zs</a>      <a id="4324" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">#⟨</a> <a id="4327" href="Chapter.Fun.SortedLists.html#6440" class="InductiveConstructor">#cong</a> <a id="4333" href="Chapter.Fun.IntrinsicInsertionSort.html#4269" class="Bound">π</a> <a id="4335" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">⟩</a>
    <a id="4341" class="Bound">y</a> <a id="4343" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4346" class="Bound">x</a> <a id="4348" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4351" class="Bound">ys</a> <a id="4354" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">#⟨</a> <a id="4357" href="Chapter.Fun.SortedLists.html#6374" class="InductiveConstructor">#swap</a> <a id="4363" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">⟩</a>
    <a id="4369" class="Bound">x</a> <a id="4371" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4374" class="Bound">y</a> <a id="4376" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4379" class="Bound">ys</a>
  <a id="4384" href="Chapter.Fun.SortedLists.html#7332" class="Function Operator">#end</a><a id="4388" class="Symbol">)</a> <a id="4390" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
  <a id="4394" href="Chapter.Fun.SortedLists.html#4541" class="InductiveConstructor">sorted-::</a> <a id="4404" class="Symbol">(</a><a id="4405" href="Chapter.Fun.SortedLists.html#8957" class="Function">lower-bound-permutation</a> <a id="4429" href="Chapter.Fun.IntrinsicInsertionSort.html#4269" class="Bound">π</a> <a id="4431" class="Symbol">(</a><a id="4432" href="Chapter.Fun.SortedLists.html#3564" class="InductiveConstructor">lb-::</a> <a id="4438" class="Bound">y≤x</a> <a id="4442" class="Bound">y≤ys</a><a id="4446" class="Symbol">))</a> <a id="4449" href="Chapter.Fun.IntrinsicInsertionSort.html#4273" class="Bound">zs-sorted</a>
</pre>
## Intrinsically verified insertion sort

We are now ready to complete the intrinsic verification of insertion
sort.

<pre class="Agda"><a id="verified-insertion-sort"></a><a id="4586" href="Chapter.Fun.IntrinsicInsertionSort.html#4586" class="Function">verified-insertion-sort</a> <a id="4610" class="Symbol">:</a> <a id="4612" href="Chapter.Fun.SortedLists.html#8800" class="Function">SortingFunction</a>
</pre>
In the base case, when the list to be sorted is empty, there isn't
much to do except providing the easy proofs that the empty list is
sorted and a permutation of itself.

<pre class="Agda"><a id="4808" href="Chapter.Fun.IntrinsicInsertionSort.html#4586" class="Function">verified-insertion-sort</a> <a id="4832" href="Library.List.html#113" class="InductiveConstructor">[]</a> <a id="4835" class="Symbol">=</a> <a id="4837" href="Library.List.html#113" class="InductiveConstructor">[]</a> <a id="4840" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="4842" href="Chapter.Fun.SortedLists.html#6338" class="InductiveConstructor">#refl</a> <a id="4848" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="4850" href="Chapter.Fun.SortedLists.html#4517" class="InductiveConstructor">sorted-[]</a>
</pre>
In the inductive case, first of all we recursively sort the tail of
the list.

<pre class="Agda"><a id="4948" href="Chapter.Fun.IntrinsicInsertionSort.html#4586" class="Function">verified-insertion-sort</a> <a id="4972" class="Symbol">(</a><a id="4973" href="Chapter.Fun.IntrinsicInsertionSort.html#4973" class="Bound">x</a> <a id="4975" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="4978" href="Chapter.Fun.IntrinsicInsertionSort.html#4978" class="Bound">xs</a><a id="4980" class="Symbol">)</a> <a id="4982" class="Keyword">with</a> <a id="4987" href="Chapter.Fun.IntrinsicInsertionSort.html#4586" class="Function">verified-insertion-sort</a> <a id="5011" href="Chapter.Fun.IntrinsicInsertionSort.html#4978" class="Bound">xs</a>
</pre>
By performing case analysis we get access to the resulting list
`ys`, a proof `ys#xs` that `ys` is a permutation of `xs` and a proof
`ys-sorted` that `ys` is sorted. Now we can insert `x` into `ys`.

<pre class="Agda"><a id="5223" class="Symbol">...</a> <a id="5227" class="Symbol">|</a> <a id="5229" href="Chapter.Fun.IntrinsicInsertionSort.html#5229" class="Bound">ys</a> <a id="5232" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="5234" href="Chapter.Fun.IntrinsicInsertionSort.html#5234" class="Bound">ys#xs</a> <a id="5240" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="5242" href="Chapter.Fun.IntrinsicInsertionSort.html#5242" class="Bound">ys-sorted</a> <a id="5252" class="Keyword">with</a> <a id="5257" href="Chapter.Fun.IntrinsicInsertionSort.html#1635" class="Function">intrinsic-insert</a> <a id="5274" class="Bound">x</a> <a id="5276" href="Chapter.Fun.IntrinsicInsertionSort.html#5229" class="Bound">ys</a> <a id="5279" href="Chapter.Fun.IntrinsicInsertionSort.html#5242" class="Bound">ys-sorted</a>
</pre>
We do case analysis on the result once again so that we get access
to the resulting list `zs`, the proof `π` that `zs` is a permutation
of `x :: ys` and the proof `zs-sorted` that `zs` is sorted. The
proof that `zs` is a permutation of `x :: xs` follows from
transitivity of permutations and the sub-proofs `ys#xs` and `π`.

<pre class="Agda"><a id="5623" class="Symbol">...</a> <a id="5627" class="Symbol">|</a> <a id="5629" href="Chapter.Fun.IntrinsicInsertionSort.html#5629" class="Bound">zs</a> <a id="5632" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="5634" href="Chapter.Fun.IntrinsicInsertionSort.html#5634" class="Bound">π</a> <a id="5636" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="5638" href="Chapter.Fun.IntrinsicInsertionSort.html#5638" class="Bound">zs-sorted</a> <a id="5648" class="Symbol">=</a>
  <a id="5652" href="Chapter.Fun.IntrinsicInsertionSort.html#5629" class="Bound">zs</a> <a id="5655" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
  <a id="5659" class="Symbol">(</a><a id="5660" href="Chapter.Fun.SortedLists.html#7256" class="Function Operator">#begin</a>
    <a id="5671" href="Chapter.Fun.IntrinsicInsertionSort.html#5629" class="Bound">zs</a>      <a id="5679" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">#⟨</a> <a id="5682" href="Chapter.Fun.IntrinsicInsertionSort.html#5634" class="Bound">π</a> <a id="5684" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">⟩</a>
    <a id="5690" class="Bound">x</a> <a id="5692" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="5695" class="Bound">ys</a> <a id="5698" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">#⟨</a> <a id="5701" href="Chapter.Fun.SortedLists.html#6440" class="InductiveConstructor">#cong</a> <a id="5707" class="Bound">ys#xs</a> <a id="5713" href="Chapter.Fun.SortedLists.html#7393" class="Function Operator">⟩</a>
    <a id="5719" class="Bound">x</a> <a id="5721" href="Library.List.html#129" class="InductiveConstructor Operator">::</a> <a id="5724" class="Bound">xs</a>
  <a id="5729" href="Chapter.Fun.SortedLists.html#7332" class="Function Operator">#end</a><a id="5733" class="Symbol">)</a> <a id="5735" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a>
  <a id="5739" href="Chapter.Fun.IntrinsicInsertionSort.html#5638" class="Bound">zs-sorted</a>
</pre>