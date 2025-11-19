---
title: "Soundness of Hoare Logic"
prev:  Chapter.Imp.HoareLogicExample
next:  Chapter.Imp.HoareLogicCompleteness
---
  
<pre class="Agda"><a id="129" class="Keyword">module</a> <a id="136" href="Chapter.Imp.HoareLogicSoundness.html" class="Module">Chapter.Imp.HoareLogicSoundness</a> <a id="168" class="Keyword">where</a>
</pre> 
## Imports 

<pre class="Agda"><a id="197" class="Keyword">open</a> <a id="202" class="Keyword">import</a> <a id="209" href="Library.Bool.html" class="Module">Library.Bool</a>
<a id="222" class="Keyword">open</a> <a id="227" class="Keyword">import</a> <a id="234" href="Library.Nat.html" class="Module">Library.Nat</a>
<a id="246" class="Keyword">open</a> <a id="251" class="Keyword">import</a> <a id="258" href="Library.Nat.Properties.html" class="Module">Library.Nat.Properties</a>
<a id="281" class="Keyword">open</a> <a id="286" class="Keyword">import</a> <a id="293" href="Library.Logic.html" class="Module">Library.Logic</a>
<a id="307" class="Keyword">open</a> <a id="312" class="Keyword">import</a> <a id="319" href="Library.Logic.Laws.html" class="Module">Library.Logic.Laws</a>
<a id="338" class="Keyword">open</a> <a id="343" class="Keyword">import</a> <a id="350" href="Library.Equality.html" class="Module">Library.Equality</a>
<a id="367" class="Keyword">open</a> <a id="372" class="Keyword">import</a> <a id="379" href="Library.Equality.Reasoning.html" class="Module">Library.Equality.Reasoning</a>

<a id="407" class="Keyword">open</a> <a id="412" class="Keyword">import</a> <a id="419" href="Chapter.Imp.AexpBexp.html" class="Module">Chapter.Imp.AexpBexp</a>
<a id="440" class="Keyword">open</a> <a id="445" class="Keyword">import</a> <a id="452" href="Chapter.Imp.BigStep.html" class="Module">Chapter.Imp.BigStep</a>
<a id="472" class="Keyword">open</a> <a id="477" class="Keyword">import</a> <a id="484" href="Chapter.Imp.HoareLogic.html" class="Module">Chapter.Imp.HoareLogic</a>
</pre>

Formalizing the partial correctness criterion into a definition, we say that
the triple `[ P ] c [ Q ]` is **valid** if for all `s, t ∈ State` whenever `P` holds of `s` and
`⦅ c , s ⦆` converges to `t`, `Q` holds of `t`. Formally, we define the following predicate: 

<pre class="Agda"><a id="|=_"></a><a id="785" href="Chapter.Imp.HoareLogicSoundness.html#785" class="Function Operator">|=_</a> <a id="789" class="Symbol">:</a> <a id="791" href="Chapter.Imp.HoareLogic.html#2525" class="Datatype">Triple</a> <a id="798" class="Symbol">-&gt;</a> <a id="801" href="Agda.Primitive.html#388" class="Primitive">Set</a>
<a id="805" href="Chapter.Imp.HoareLogicSoundness.html#785" class="Function Operator">|=</a> <a id="808" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="810" href="Chapter.Imp.HoareLogicSoundness.html#810" class="Bound">P</a> <a id="812" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="814" href="Chapter.Imp.HoareLogicSoundness.html#814" class="Bound">c</a> <a id="816" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="818" href="Chapter.Imp.HoareLogicSoundness.html#818" class="Bound">Q</a> <a id="820" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="822" class="Symbol">=</a> <a id="824" class="Symbol">∀</a> <a id="826" class="Symbol">{</a><a id="827" href="Chapter.Imp.HoareLogicSoundness.html#827" class="Bound">s</a> <a id="829" href="Chapter.Imp.HoareLogicSoundness.html#829" class="Bound">t</a><a id="830" class="Symbol">}</a> <a id="832" class="Symbol">-&gt;</a> <a id="835" href="Chapter.Imp.HoareLogicSoundness.html#810" class="Bound">P</a> <a id="837" href="Chapter.Imp.HoareLogicSoundness.html#827" class="Bound">s</a> <a id="839" class="Symbol">-&gt;</a> <a id="842" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦅</a> <a id="844" href="Chapter.Imp.HoareLogicSoundness.html#814" class="Bound">c</a> <a id="846" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">,</a> <a id="848" href="Chapter.Imp.HoareLogicSoundness.html#827" class="Bound">s</a> <a id="850" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦆</a> <a id="852" href="Chapter.Imp.BigStep.html#3810" class="Datatype Operator">⇒</a> <a id="854" href="Chapter.Imp.HoareLogicSoundness.html#829" class="Bound">t</a> <a id="856" class="Symbol">-&gt;</a> <a id="859" href="Chapter.Imp.HoareLogicSoundness.html#818" class="Bound">Q</a> <a id="861" href="Chapter.Imp.HoareLogicSoundness.html#829" class="Bound">t</a>
</pre>
Hoare Logic is intended to provide a tool to establish when a triple is valid.
To ensure that this is the case, we show that the system is **sound**  i.e. that only
valid triples are derivable. This is the content of `theorem-Hoare-sound` claiming the
implication

                    ∀ {P c Q} ->  |- [ P ] c [ Q ]  ->  |= [ P ] c [ Q ]

The strategy to prove the theorem is first to show that all instances of axioms `H-Skip` and `H-Loc`
are valid triples, which is immediate. Then the actual task in the proof is to show that
the remaining rules infer valid triples from valid ones instantiating the respective
premises. All in all, this is a proof by structural induction on the derivation of
`|- [ P ] c [ Q ]`.

Going through the proof, we realise that the thesis is an easy consequence of the induction
hypotheses in all cases but in case of rule `H-While`, which deserves a more careful inspection.
In Hoare system the rule is written:

                                  {P ∧ b} c {P}
                            -------------------------
                            {P} WHILE b DO c {P ∧ ¬ b}

where `P` is the **loop invariant**, which is assumed to hold before executing the command
`WHILE b DO c` and to be preserved by the execution of the body `c` whenever
the condition of the guard `b` is true. From such hypotheses and the hypothesis
that the execution of `WHILE b DO c` terminates, the rule infers that the post-condition
of this loop is `P ∧ ¬ b`, where `¬ b` expresses the fact that for a `WHILE` command to
terminate the guard must be eventually false.

In our system the above rule is encoded by

           H-While : ∀ {P b c}
                   -> |- [ (λ s -> P s ∧ bval b s == true) ] c [ P ]
                   ---------------------------------------------------------------
                   -> |- [ P ] (WHILE b DO c) [ (λ s -> P s ∧ bval b s == false) ]
 
To simplify the proof of the theorem, we begin with two lemmas stating respectively
that under the hypothesis that `[ (λ s -> P s ∧ bval b s == true) ] c [ P ]` is valid,
the assertion `P` is a loop invariant for `WHILE b DO c` and that if its execution
terminates in a state `t` then `bval b t == false`.

<pre class="Agda"><a id="lemma-Hoare-inv"></a><a id="3066" href="Chapter.Imp.HoareLogicSoundness.html#3066" class="Function">lemma-Hoare-inv</a> <a id="3082" class="Symbol">:</a> <a id="3084" class="Symbol">∀</a> <a id="3086" class="Symbol">{</a><a id="3087" href="Chapter.Imp.HoareLogicSoundness.html#3087" class="Bound">P</a> <a id="3089" class="Symbol">:</a> <a id="3091" href="Chapter.Imp.HoareLogic.html#2499" class="Function">Assn</a><a id="3095" class="Symbol">}</a> <a id="3097" class="Symbol">{</a><a id="3098" href="Chapter.Imp.HoareLogicSoundness.html#3098" class="Bound">s</a> <a id="3100" href="Chapter.Imp.HoareLogicSoundness.html#3100" class="Bound">b</a> <a id="3102" href="Chapter.Imp.HoareLogicSoundness.html#3102" class="Bound">c</a> <a id="3104" href="Chapter.Imp.HoareLogicSoundness.html#3104" class="Bound">t</a><a id="3105" class="Symbol">}</a> <a id="3107" class="Symbol">-&gt;</a>
                  <a id="3128" class="Symbol">(∀{</a><a id="3131" href="Chapter.Imp.HoareLogicSoundness.html#3131" class="Bound">s&#39;</a> <a id="3134" href="Chapter.Imp.HoareLogicSoundness.html#3134" class="Bound">t&#39;</a><a id="3136" class="Symbol">}</a> <a id="3138" class="Symbol">-&gt;</a> <a id="3141" class="Symbol">(</a><a id="3142" href="Chapter.Imp.HoareLogicSoundness.html#3087" class="Bound">P</a> <a id="3144" href="Chapter.Imp.HoareLogicSoundness.html#3131" class="Bound">s&#39;</a> <a id="3147" href="Library.Logic.html#1349" class="Function Operator">∧</a> <a id="3149" href="Chapter.Imp.AexpBexp.html#10249" class="Function">bval</a> <a id="3154" href="Chapter.Imp.HoareLogicSoundness.html#3100" class="Bound">b</a> <a id="3156" href="Chapter.Imp.HoareLogicSoundness.html#3131" class="Bound">s&#39;</a> <a id="3159" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="3162" href="Library.Bool.html#52" class="InductiveConstructor">true</a><a id="3166" class="Symbol">)</a> <a id="3168" class="Symbol">-&gt;</a>
                               <a id="3202" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦅</a> <a id="3204" href="Chapter.Imp.HoareLogicSoundness.html#3102" class="Bound">c</a> <a id="3206" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">,</a> <a id="3208" href="Chapter.Imp.HoareLogicSoundness.html#3131" class="Bound">s&#39;</a> <a id="3211" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦆</a> <a id="3213" href="Chapter.Imp.BigStep.html#3810" class="Datatype Operator">⇒</a> <a id="3215" href="Chapter.Imp.HoareLogicSoundness.html#3134" class="Bound">t&#39;</a>
                               <a id="3249" class="Symbol">-&gt;</a> <a id="3252" href="Chapter.Imp.HoareLogicSoundness.html#3087" class="Bound">P</a> <a id="3254" href="Chapter.Imp.HoareLogicSoundness.html#3134" class="Bound">t&#39;</a><a id="3256" class="Symbol">)</a> <a id="3258" class="Symbol">-&gt;</a>
                  <a id="3279" href="Chapter.Imp.HoareLogicSoundness.html#3087" class="Bound">P</a> <a id="3281" href="Chapter.Imp.HoareLogicSoundness.html#3098" class="Bound">s</a> <a id="3283" class="Symbol">-&gt;</a>
                  <a id="3304" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦅</a> <a id="3306" href="Chapter.Imp.BigStep.html#1738" class="InductiveConstructor Operator">WHILE</a> <a id="3312" href="Chapter.Imp.HoareLogicSoundness.html#3100" class="Bound">b</a> <a id="3314" href="Chapter.Imp.BigStep.html#1738" class="InductiveConstructor Operator">DO</a> <a id="3317" href="Chapter.Imp.HoareLogicSoundness.html#3102" class="Bound">c</a> <a id="3319" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">,</a> <a id="3321" href="Chapter.Imp.HoareLogicSoundness.html#3098" class="Bound">s</a> <a id="3323" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦆</a> <a id="3325" href="Chapter.Imp.BigStep.html#3810" class="Datatype Operator">⇒</a> <a id="3327" href="Chapter.Imp.HoareLogicSoundness.html#3104" class="Bound">t</a> <a id="3329" class="Symbol">-&gt;</a>
                  <a id="3350" href="Chapter.Imp.HoareLogicSoundness.html#3087" class="Bound">P</a> <a id="3352" href="Chapter.Imp.HoareLogicSoundness.html#3104" class="Bound">t</a>
                  
<a id="3373" href="Chapter.Imp.HoareLogicSoundness.html#3066" class="Function">lemma-Hoare-inv</a> <a id="3389" class="Symbol">{</a><a id="3390" href="Chapter.Imp.HoareLogicSoundness.html#3390" class="Bound">P</a><a id="3391" class="Symbol">}</a> <a id="3393" class="Symbol">{</a><a id="3394" href="Chapter.Imp.HoareLogicSoundness.html#3394" class="Bound">s</a><a id="3395" class="Symbol">}</a> <a id="3397" class="Symbol">{</a><a id="3398" href="Chapter.Imp.HoareLogicSoundness.html#3398" class="Bound">b</a><a id="3399" class="Symbol">}</a> <a id="3401" class="Symbol">{</a><a id="3402" href="Chapter.Imp.HoareLogicSoundness.html#3402" class="Bound">c</a><a id="3403" class="Symbol">}</a> <a id="3405" class="Symbol">{</a><a id="3406" class="DottedPattern Symbol">.</a><a id="3407" href="Chapter.Imp.HoareLogicSoundness.html#3394" class="DottedPattern Bound">s</a><a id="3408" class="Symbol">}</a> <a id="3410" href="Chapter.Imp.HoareLogicSoundness.html#3410" class="Bound">hyp1</a> <a id="3415" href="Chapter.Imp.HoareLogicSoundness.html#3415" class="Bound">hyp2</a> <a id="3420" class="Symbol">(</a><a id="3421" href="Chapter.Imp.BigStep.html#4569" class="InductiveConstructor">WhileFalse</a> <a id="3432" href="Chapter.Imp.HoareLogicSoundness.html#3432" class="Bound">x</a><a id="3433" class="Symbol">)</a> <a id="3435" class="Symbol">=</a> <a id="3437" href="Chapter.Imp.HoareLogicSoundness.html#3415" class="Bound">hyp2</a>
<a id="3442" href="Chapter.Imp.HoareLogicSoundness.html#3066" class="Function">lemma-Hoare-inv</a> <a id="3458" class="Symbol">{</a><a id="3459" href="Chapter.Imp.HoareLogicSoundness.html#3459" class="Bound">P</a><a id="3460" class="Symbol">}</a> <a id="3462" class="Symbol">{</a><a id="3463" href="Chapter.Imp.HoareLogicSoundness.html#3463" class="Bound">s</a><a id="3464" class="Symbol">}</a> <a id="3466" class="Symbol">{</a><a id="3467" href="Chapter.Imp.HoareLogicSoundness.html#3467" class="Bound">b</a><a id="3468" class="Symbol">}</a> <a id="3470" class="Symbol">{</a><a id="3471" href="Chapter.Imp.HoareLogicSoundness.html#3471" class="Bound">c</a><a id="3472" class="Symbol">}</a> <a id="3474" class="Symbol">{</a><a id="3475" href="Chapter.Imp.HoareLogicSoundness.html#3475" class="Bound">t</a><a id="3476" class="Symbol">}</a> <a id="3478" href="Chapter.Imp.HoareLogicSoundness.html#3478" class="Bound">hyp1</a> <a id="3483" href="Chapter.Imp.HoareLogicSoundness.html#3483" class="Bound">hyp2</a>
           <a id="3499" class="Symbol">(</a><a id="3500" href="Chapter.Imp.BigStep.html#4727" class="InductiveConstructor">WhileTrue</a> <a id="3510" class="Symbol">{</a><a id="3511" class="DottedPattern Symbol">.</a><a id="3512" href="Chapter.Imp.HoareLogicSoundness.html#3471" class="DottedPattern Bound">c</a><a id="3513" class="Symbol">}</a> <a id="3515" class="Symbol">{</a><a id="3516" class="DottedPattern Symbol">.</a><a id="3517" href="Chapter.Imp.HoareLogicSoundness.html#3467" class="DottedPattern Bound">b</a><a id="3518" class="Symbol">}</a> <a id="3520" class="Symbol">{</a><a id="3521" class="DottedPattern Symbol">.</a><a id="3522" href="Chapter.Imp.HoareLogicSoundness.html#3463" class="DottedPattern Bound">s</a><a id="3523" class="Symbol">}</a> <a id="3525" class="Symbol">{</a><a id="3526" href="Chapter.Imp.HoareLogicSoundness.html#3526" class="Bound">s&#39;</a><a id="3528" class="Symbol">}</a> <a id="3530" class="Symbol">{</a><a id="3531" href="Chapter.Imp.HoareLogicSoundness.html#3531" class="Bound">s&#39;&#39;</a><a id="3534" class="Symbol">}</a> <a id="3536" href="Chapter.Imp.HoareLogicSoundness.html#3536" class="Bound">x</a> <a id="3538" href="Chapter.Imp.HoareLogicSoundness.html#3538" class="Bound">hyp3</a> <a id="3543" href="Chapter.Imp.HoareLogicSoundness.html#3543" class="Bound">hyp4</a><a id="3547" class="Symbol">)</a> <a id="3549" class="Symbol">=</a> <a id="3551" href="Chapter.Imp.HoareLogicSoundness.html#3638" class="Function">claim2</a> 
     <a id="3564" class="Keyword">where</a>
       <a id="3577" href="Chapter.Imp.HoareLogicSoundness.html#3577" class="Function">claim1</a> <a id="3584" class="Symbol">=</a> <a id="3586" href="Chapter.Imp.HoareLogicSoundness.html#3478" class="Bound">hyp1</a> <a id="3591" class="Symbol">{</a><a id="3592" href="Chapter.Imp.HoareLogicSoundness.html#3463" class="Bound">s</a><a id="3593" class="Symbol">}</a> <a id="3595" class="Symbol">{</a><a id="3596" href="Chapter.Imp.HoareLogicSoundness.html#3526" class="Bound">s&#39;</a><a id="3598" class="Symbol">}</a> <a id="3600" class="Symbol">(</a><a id="3601" href="Chapter.Imp.HoareLogicSoundness.html#3483" class="Bound">hyp2</a> <a id="3606" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="3608" href="Chapter.Imp.HoareLogicSoundness.html#3536" class="Bound">x</a><a id="3609" class="Symbol">)</a> <a id="3611" href="Chapter.Imp.HoareLogicSoundness.html#3538" class="Bound">hyp3</a>               
       <a id="3638" href="Chapter.Imp.HoareLogicSoundness.html#3638" class="Function">claim2</a> <a id="3645" class="Symbol">=</a> <a id="3647" href="Chapter.Imp.HoareLogicSoundness.html#3066" class="Function">lemma-Hoare-inv</a> <a id="3663" class="Symbol">{</a><a id="3664" href="Chapter.Imp.HoareLogicSoundness.html#3459" class="Bound">P</a><a id="3665" class="Symbol">}</a> <a id="3667" class="Symbol">{</a><a id="3668" href="Chapter.Imp.HoareLogicSoundness.html#3526" class="Bound">s&#39;</a><a id="3670" class="Symbol">}</a> <a id="3672" class="Symbol">{</a><a id="3673" href="Chapter.Imp.HoareLogicSoundness.html#3467" class="Bound">b</a><a id="3674" class="Symbol">}</a> <a id="3676" class="Symbol">{</a><a id="3677" href="Chapter.Imp.HoareLogicSoundness.html#3471" class="Bound">c</a><a id="3678" class="Symbol">}</a> <a id="3680" class="Symbol">{</a><a id="3681" href="Chapter.Imp.HoareLogicSoundness.html#3475" class="Bound">t</a><a id="3682" class="Symbol">}</a>
                                  <a id="3718" class="Symbol">(</a><a id="3719" href="Chapter.Imp.HoareLogicSoundness.html#3478" class="Bound">hyp1</a> <a id="3724" class="Symbol">{_}</a> <a id="3728" class="Symbol">{_})</a> <a id="3733" href="Chapter.Imp.HoareLogicSoundness.html#3577" class="Function">claim1</a> <a id="3740" href="Chapter.Imp.HoareLogicSoundness.html#3543" class="Bound">hyp4</a>

<a id="lemma-Hoare-loop-exit"></a><a id="3746" href="Chapter.Imp.HoareLogicSoundness.html#3746" class="Function">lemma-Hoare-loop-exit</a> <a id="3768" class="Symbol">:</a> <a id="3770" class="Symbol">∀</a> <a id="3772" class="Symbol">{</a><a id="3773" href="Chapter.Imp.HoareLogicSoundness.html#3773" class="Bound">b</a> <a id="3775" href="Chapter.Imp.HoareLogicSoundness.html#3775" class="Bound">c</a> <a id="3777" href="Chapter.Imp.HoareLogicSoundness.html#3777" class="Bound">s</a> <a id="3779" href="Chapter.Imp.HoareLogicSoundness.html#3779" class="Bound">t</a><a id="3780" class="Symbol">}</a>
             <a id="3795" class="Symbol">-&gt;</a> <a id="3798" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦅</a> <a id="3800" href="Chapter.Imp.BigStep.html#1738" class="InductiveConstructor Operator">WHILE</a> <a id="3806" href="Chapter.Imp.HoareLogicSoundness.html#3773" class="Bound">b</a> <a id="3808" href="Chapter.Imp.BigStep.html#1738" class="InductiveConstructor Operator">DO</a> <a id="3811" href="Chapter.Imp.HoareLogicSoundness.html#3775" class="Bound">c</a> <a id="3813" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">,</a> <a id="3815" href="Chapter.Imp.HoareLogicSoundness.html#3777" class="Bound">s</a> <a id="3817" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦆</a> <a id="3819" href="Chapter.Imp.BigStep.html#3810" class="Datatype Operator">⇒</a> <a id="3821" href="Chapter.Imp.HoareLogicSoundness.html#3779" class="Bound">t</a> <a id="3823" class="Symbol">-&gt;</a> <a id="3826" href="Chapter.Imp.AexpBexp.html#10249" class="Function">bval</a> <a id="3831" href="Chapter.Imp.HoareLogicSoundness.html#3773" class="Bound">b</a> <a id="3833" href="Chapter.Imp.HoareLogicSoundness.html#3779" class="Bound">t</a> <a id="3835" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="3838" href="Library.Bool.html#57" class="InductiveConstructor">false</a> 

<a id="3846" href="Chapter.Imp.HoareLogicSoundness.html#3746" class="Function">lemma-Hoare-loop-exit</a> <a id="3868" class="Symbol">(</a><a id="3869" href="Chapter.Imp.BigStep.html#4569" class="InductiveConstructor">WhileFalse</a> <a id="3880" href="Chapter.Imp.HoareLogicSoundness.html#3880" class="Bound">x</a><a id="3881" class="Symbol">)</a> <a id="3883" class="Symbol">=</a> <a id="3885" href="Chapter.Imp.HoareLogicSoundness.html#3880" class="Bound">x</a>
<a id="3887" href="Chapter.Imp.HoareLogicSoundness.html#3746" class="Function">lemma-Hoare-loop-exit</a> <a id="3909" class="Symbol">(</a><a id="3910" href="Chapter.Imp.BigStep.html#4727" class="InductiveConstructor">WhileTrue</a> <a id="3920" href="Chapter.Imp.HoareLogicSoundness.html#3920" class="Bound">x</a> <a id="3922" href="Chapter.Imp.HoareLogicSoundness.html#3922" class="Bound">hyp1</a> <a id="3927" href="Chapter.Imp.HoareLogicSoundness.html#3927" class="Bound">hyp2</a><a id="3931" class="Symbol">)</a> <a id="3933" class="Symbol">=</a>
                                  <a id="3969" href="Chapter.Imp.HoareLogicSoundness.html#3746" class="Function">lemma-Hoare-loop-exit</a> <a id="3991" href="Chapter.Imp.HoareLogicSoundness.html#3927" class="Bound">hyp2</a>
</pre>
Technically we observe the usage of implicit arguments in the proof of
`lemma-Hoare-inv` and in particular of dot patterns
Implicit arguments are necessary to distinguish
the states `s', s''` from `s`: indeed the formers are automatically generated by Agda
when splitting the hypothesis `⦅ WHILE b DO c , s ⦆ ⇒ s''` of the inductive case into
`⦅ c , s ⦆ ⇒ s'` and `⦅ WHILE b DO c , s' ⦆ ⇒ s''`, so that without passing the implicit arguments
to `WhileTrue` they are not in scope and hence inaccessible.

Dot patterns are constraints used by Agda to enforce the same binding of several occurrences
of a variable in a non linear pattern: for example the variable `{.c}` has to be bound to the
same command as the previous variable `{c}`. For explanations about dot patterns see
[Function Definitions - Dot patterns](https://agda.readthedocs.io/en/v2.5.2/language/function-definitions.html)
in Agda documentation. 

We are eventually in place to prove `theorem-Hoare-sound` which is a corollary of
`lemma-Hoare-sound` that establishes the same thesis but in a more explicit form, which
allows the access to those implicit parameters which are essential in the proof of the
theorem.

<pre class="Agda"><a id="lemma-Hoare-sound"></a><a id="5185" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="5203" class="Symbol">:</a> <a id="5205" class="Symbol">∀</a> <a id="5207" class="Symbol">{</a><a id="5208" href="Chapter.Imp.HoareLogicSoundness.html#5208" class="Bound">P</a> <a id="5210" href="Chapter.Imp.HoareLogicSoundness.html#5210" class="Bound">c</a> <a id="5212" href="Chapter.Imp.HoareLogicSoundness.html#5212" class="Bound">Q</a> <a id="5214" href="Chapter.Imp.HoareLogicSoundness.html#5214" class="Bound">s</a> <a id="5216" href="Chapter.Imp.HoareLogicSoundness.html#5216" class="Bound">t</a><a id="5217" class="Symbol">}</a> <a id="5219" class="Symbol">-&gt;</a>
             <a id="5235" href="Chapter.Imp.HoareLogic.html#4019" class="Datatype Operator">|-</a> <a id="5238" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="5240" href="Chapter.Imp.HoareLogicSoundness.html#5208" class="Bound">P</a> <a id="5242" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="5244" href="Chapter.Imp.HoareLogicSoundness.html#5210" class="Bound">c</a> <a id="5246" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="5248" href="Chapter.Imp.HoareLogicSoundness.html#5212" class="Bound">Q</a> <a id="5250" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="5252" class="Symbol">-&gt;</a> 
             <a id="5269" href="Chapter.Imp.HoareLogicSoundness.html#5208" class="Bound">P</a> <a id="5271" href="Chapter.Imp.HoareLogicSoundness.html#5214" class="Bound">s</a> <a id="5273" class="Symbol">-&gt;</a> 
             <a id="5290" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦅</a> <a id="5292" href="Chapter.Imp.HoareLogicSoundness.html#5210" class="Bound">c</a> <a id="5294" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">,</a> <a id="5296" href="Chapter.Imp.HoareLogicSoundness.html#5214" class="Bound">s</a> <a id="5298" href="Chapter.Imp.BigStep.html#3329" class="InductiveConstructor Operator">⦆</a> <a id="5300" href="Chapter.Imp.BigStep.html#3810" class="Datatype Operator">⇒</a> <a id="5302" href="Chapter.Imp.HoareLogicSoundness.html#5216" class="Bound">t</a> <a id="5304" class="Symbol">-&gt;</a> 
             <a id="5321" href="Chapter.Imp.HoareLogicSoundness.html#5212" class="Bound">Q</a> <a id="5323" href="Chapter.Imp.HoareLogicSoundness.html#5216" class="Bound">t</a>
</pre>To facilitate the understanding of the proof we
intersperse the cases with some comments drown from the interactive construction of the proof itself.
As a first step in the proof we write

                     lemma-Hoare-sound hyp1 hyp2 hyp3 = ?

and then we hit `C-c C-c` twice splitting `hyp1 :  |- [ P ] c [ Q ]` and
`hyp3 :  ⦅ c , s ⦆ ⇒ t`.

<pre class="Agda"><a id="5680" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="5698" href="Chapter.Imp.HoareLogic.html#4051" class="InductiveConstructor">H-Skip</a> <a id="5705" href="Chapter.Imp.HoareLogicSoundness.html#5705" class="Bound">hyp2</a> <a id="5710" href="Chapter.Imp.BigStep.html#3849" class="InductiveConstructor">Skip</a> <a id="5715" class="Symbol">=</a> <a id="5717" href="Chapter.Imp.HoareLogicSoundness.html#5705" class="Bound">hyp2</a>

<a id="5723" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="5741" href="Chapter.Imp.HoareLogic.html#4136" class="InductiveConstructor">H-Loc</a> <a id="5747" href="Chapter.Imp.HoareLogicSoundness.html#5747" class="Bound">hyp2</a> <a id="5752" href="Chapter.Imp.BigStep.html#3921" class="InductiveConstructor">Loc</a> <a id="5756" class="Symbol">=</a> <a id="5758" href="Chapter.Imp.HoareLogicSoundness.html#5747" class="Bound">hyp2</a>
</pre>In cases of `H-Skip` and `H-Loc` the hypothesis `hyp2` in
the left-hand sides has the types `P s` and
`Q (s [ x ::= aval a s ])` respectively.
These are the same as the types of the respective right-hand sides, hence they
are both authomatically obtained typing `C-c C-a` while putting the cursor in the holes.
 
<pre class="Agda"><a id="6084" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="6102" class="Symbol">(</a><a id="6103" href="Chapter.Imp.HoareLogic.html#4297" class="InductiveConstructor">H-Comp</a> <a id="6110" href="Chapter.Imp.HoareLogicSoundness.html#6110" class="Bound">hyp1</a> <a id="6115" href="Chapter.Imp.HoareLogicSoundness.html#6115" class="Bound">hyp4</a><a id="6119" class="Symbol">)</a> <a id="6121" href="Chapter.Imp.HoareLogicSoundness.html#6121" class="Bound">hyp2</a> <a id="6126" class="Symbol">(</a><a id="6127" href="Chapter.Imp.BigStep.html#4039" class="InductiveConstructor">Comp</a> <a id="6132" href="Chapter.Imp.HoareLogicSoundness.html#6132" class="Bound">hyp3</a> <a id="6137" href="Chapter.Imp.HoareLogicSoundness.html#6137" class="Bound">hyp5</a><a id="6141" class="Symbol">)</a> <a id="6143" class="Symbol">=</a> <a id="6145" href="Chapter.Imp.HoareLogicSoundness.html#6218" class="Function">IH2</a>
      <a id="6155" class="Keyword">where</a>
         <a id="6170" href="Chapter.Imp.HoareLogicSoundness.html#6170" class="Function">IH1</a> <a id="6174" class="Symbol">=</a> <a id="6176" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="6194" href="Chapter.Imp.HoareLogicSoundness.html#6110" class="Bound">hyp1</a> <a id="6199" href="Chapter.Imp.HoareLogicSoundness.html#6121" class="Bound">hyp2</a> <a id="6204" href="Chapter.Imp.HoareLogicSoundness.html#6132" class="Bound">hyp3</a>
         <a id="6218" href="Chapter.Imp.HoareLogicSoundness.html#6218" class="Function">IH2</a> <a id="6222" class="Symbol">=</a> <a id="6224" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="6242" href="Chapter.Imp.HoareLogicSoundness.html#6115" class="Bound">hyp4</a> <a id="6247" href="Chapter.Imp.HoareLogicSoundness.html#6170" class="Function">IH1</a> <a id="6251" href="Chapter.Imp.HoareLogicSoundness.html#6137" class="Bound">hyp5</a>
</pre>In case of `H-Comp`, typing

          lemma-Hoare-sound (H-Comp hyp1 hyp4) hyp2 (Comp hyp3 hyp5) = ?

and then hitting `C-c C-,` with the cursor in the hole we obtain from Agda the reply
(omitting parameters that are not in scope): 

          Goal: Q t
          ———————————————————————————————————————————————————————
          hyp5 : ⦅ c₂ , s₂ ⦆ ⇒ t
          hyp3 : ⦅ c₁ , s ⦆ ⇒ s₂
          hyp2 : P s
          hyp4 : |- [ Q₁ ] c₂ [ Q ]
          hyp1 : |- [ P ] c₁ [ Q₁ ]

The induction hypothesis `lemma-Hoare-sound hyp1` is a proof of
`|=  [ P ] c₁ [ Q₁ ]` that is applied to `hyp2 : P s` and to `hyp3 : ⦅ c₁ , s ⦆ ⇒ s₂`
yielding a proof `IH1 : Q₁ s₂`. On the other hand
the induction hypothesis `lemma-Hoare-sound hyp4` is a proof of
`|= [ Q₁ ] c₂ [ Q ]`, that when applied to `IH1 : Q₁ s₂` and `hyp5 : ⦅ c₂ , s₂ ⦆ ⇒ t`
returns a proof of `Q t` which is the goal. 


<pre class="Agda"><a id="7142" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="7160" class="Symbol">(</a><a id="7161" href="Chapter.Imp.HoareLogic.html#4462" class="InductiveConstructor">H-If</a> <a id="7166" href="Chapter.Imp.HoareLogicSoundness.html#7166" class="Bound">hyp1</a> <a id="7171" href="Chapter.Imp.HoareLogicSoundness.html#7171" class="Bound">hyp4</a><a id="7175" class="Symbol">)</a> <a id="7177" href="Chapter.Imp.HoareLogicSoundness.html#7177" class="Bound">hyp2</a> <a id="7182" class="Symbol">(</a><a id="7183" href="Chapter.Imp.BigStep.html#4198" class="InductiveConstructor">IfTrue</a> <a id="7190" href="Chapter.Imp.HoareLogicSoundness.html#7190" class="Bound">x</a> <a id="7192" href="Chapter.Imp.HoareLogicSoundness.html#7192" class="Bound">hyp3</a><a id="7196" class="Symbol">)</a> <a id="7198" class="Symbol">=</a> <a id="7200" href="Chapter.Imp.HoareLogicSoundness.html#7264" class="Function">thesis</a>
      <a id="7213" class="Keyword">where</a>

        <a id="7228" href="Chapter.Imp.HoareLogicSoundness.html#7228" class="Function">IH</a> <a id="7231" class="Symbol">=</a> <a id="7233" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="7251" href="Chapter.Imp.HoareLogicSoundness.html#7166" class="Bound">hyp1</a>
        <a id="7264" href="Chapter.Imp.HoareLogicSoundness.html#7264" class="Function">thesis</a> <a id="7271" class="Symbol">=</a> <a id="7273" href="Chapter.Imp.HoareLogicSoundness.html#7228" class="Function">IH</a> <a id="7276" class="Symbol">(</a><a id="7277" href="Chapter.Imp.HoareLogicSoundness.html#7177" class="Bound">hyp2</a> <a id="7282" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="7284" href="Chapter.Imp.HoareLogicSoundness.html#7190" class="Bound">x</a><a id="7285" class="Symbol">)</a> <a id="7287" href="Chapter.Imp.HoareLogicSoundness.html#7192" class="Bound">hyp3</a>

<a id="7293" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="7311" class="Symbol">(</a><a id="7312" href="Chapter.Imp.HoareLogic.html#4462" class="InductiveConstructor">H-If</a> <a id="7317" href="Chapter.Imp.HoareLogicSoundness.html#7317" class="Bound">hyp1</a> <a id="7322" href="Chapter.Imp.HoareLogicSoundness.html#7322" class="Bound">hyp4</a><a id="7326" class="Symbol">)</a> <a id="7328" href="Chapter.Imp.HoareLogicSoundness.html#7328" class="Bound">hyp2</a> <a id="7333" class="Symbol">(</a><a id="7334" href="Chapter.Imp.BigStep.html#4385" class="InductiveConstructor">IfFalse</a> <a id="7342" href="Chapter.Imp.HoareLogicSoundness.html#7342" class="Bound">y</a> <a id="7344" href="Chapter.Imp.HoareLogicSoundness.html#7344" class="Bound">hyp3</a><a id="7348" class="Symbol">)</a> <a id="7350" class="Symbol">=</a> <a id="7352" href="Chapter.Imp.HoareLogicSoundness.html#7416" class="Function">thesis</a>
      <a id="7365" class="Keyword">where</a>

        <a id="7380" href="Chapter.Imp.HoareLogicSoundness.html#7380" class="Function">IH</a> <a id="7383" class="Symbol">=</a> <a id="7385" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="7403" href="Chapter.Imp.HoareLogicSoundness.html#7322" class="Bound">hyp4</a>
        <a id="7416" href="Chapter.Imp.HoareLogicSoundness.html#7416" class="Function">thesis</a> <a id="7423" class="Symbol">=</a> <a id="7425" href="Chapter.Imp.HoareLogicSoundness.html#7380" class="Function">IH</a> <a id="7428" class="Symbol">(</a><a id="7429" href="Chapter.Imp.HoareLogicSoundness.html#7328" class="Bound">hyp2</a> <a id="7434" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="7436" href="Chapter.Imp.HoareLogicSoundness.html#7342" class="Bound">y</a><a id="7437" class="Symbol">)</a> <a id="7439" href="Chapter.Imp.HoareLogicSoundness.html#7344" class="Bound">hyp3</a>
</pre>
Case `H-If` is split into two subcases according to 
the value of `b` from the command `IF b THEN c₁ ELSE c₂` in
the third hypothesis. By asking Agda about the context by means of
`C-c C-,` we get 

          Goal: Q t
          ——————————————————————————————————————————————————————
          hyp3 : ⦅ c₁ , s ⦆ ⇒ t
          x    : bval b s == true
          hyp2 : P s
          hyp4 : |- [ (λ s₁ -> P s₁ ∧ bval b s₁ == false) ] c₂ [ Q ]
          hyp1 : |- [ (λ s₁ -> P s₁ ∧ bval b s₁ == true) ] c₁ [ Q ]

In case of `(IfTrue x hyp3) : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t`
the induction hypothesis
`IH = lemma-Hoare-sound hyp1 : |= [ (λ s₁ -> P s₁ ∧ bval b s₁ == true) ] c₁ [ Q ]`
is applied to `(hyp2 , x) : P s ∧ bval b s == true` and to `hyp3 : ⦅ c₁ , s ⦆ ⇒ t`
yielding a proof `thesis : Q t` as desired.

The case `(IfFalse y hyp3) : ⦅ IF b THEN c₁ ELSE c₂ , s ⦆ ⇒ t`, where
`hyp3 : ⦅ c₂ , s ⦆ ⇒ t` and
`y : bval b s == false` is similar, using the induction
hypothesis `IH = lemma-Hoare-sound hyp4`.

<pre class="Agda"><a id="8459" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="8477" class="Symbol">{</a><a id="8478" href="Chapter.Imp.HoareLogicSoundness.html#8478" class="Bound">P</a><a id="8479" class="Symbol">}</a> <a id="8481" class="Symbol">{_}</a> <a id="8485" class="Symbol">{_}</a> <a id="8489" class="Symbol">{</a><a id="8490" href="Chapter.Imp.HoareLogicSoundness.html#8490" class="Bound">s</a><a id="8491" class="Symbol">}</a> <a id="8493" class="Symbol">{</a><a id="8494" href="Chapter.Imp.HoareLogicSoundness.html#8494" class="Bound">t</a><a id="8495" class="Symbol">}</a>
                  <a id="8515" class="Symbol">(</a><a id="8516" href="Chapter.Imp.HoareLogic.html#4726" class="InductiveConstructor">H-While</a> <a id="8524" class="Symbol">{_}</a> <a id="8528" class="Symbol">{</a><a id="8529" href="Chapter.Imp.HoareLogicSoundness.html#8529" class="Bound">b</a><a id="8530" class="Symbol">}</a> <a id="8532" href="Chapter.Imp.HoareLogicSoundness.html#8532" class="Bound">hyp1</a><a id="8536" class="Symbol">)</a> <a id="8538" href="Chapter.Imp.HoareLogicSoundness.html#8538" class="Bound">hyp2</a> <a id="8543" href="Chapter.Imp.HoareLogicSoundness.html#8543" class="Bound">hyp3</a> <a id="8548" class="Symbol">=</a> <a id="8550" href="Chapter.Imp.HoareLogicSoundness.html#8584" class="Function">Pt</a> <a id="8553" href="Library.Logic.html#271" class="InductiveConstructor Operator">,</a> <a id="8555" href="Chapter.Imp.HoareLogicSoundness.html#8668" class="Function">b-false</a>
      <a id="8569" class="Keyword">where</a>

        <a id="8584" href="Chapter.Imp.HoareLogicSoundness.html#8584" class="Function">Pt</a> <a id="8587" class="Symbol">:</a> <a id="8589" href="Chapter.Imp.HoareLogicSoundness.html#8478" class="Bound">P</a> <a id="8591" href="Chapter.Imp.HoareLogicSoundness.html#8494" class="Bound">t</a>
        <a id="8601" href="Chapter.Imp.HoareLogicSoundness.html#8584" class="Function">Pt</a> <a id="8604" class="Symbol">=</a> <a id="8606" href="Chapter.Imp.HoareLogicSoundness.html#3066" class="Function">lemma-Hoare-inv</a> <a id="8622" class="Symbol">(</a><a id="8623" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="8641" href="Chapter.Imp.HoareLogicSoundness.html#8532" class="Bound">hyp1</a> <a id="8646" class="Symbol">)</a> <a id="8648" href="Chapter.Imp.HoareLogicSoundness.html#8538" class="Bound">hyp2</a> <a id="8653" href="Chapter.Imp.HoareLogicSoundness.html#8543" class="Bound">hyp3</a> 

        <a id="8668" href="Chapter.Imp.HoareLogicSoundness.html#8668" class="Function">b-false</a> <a id="8676" class="Symbol">:</a> <a id="8678" href="Chapter.Imp.AexpBexp.html#10249" class="Function">bval</a> <a id="8683" href="Chapter.Imp.HoareLogicSoundness.html#8529" class="Bound">b</a> <a id="8685" href="Chapter.Imp.HoareLogicSoundness.html#8494" class="Bound">t</a> <a id="8687" href="Library.Equality.html#83" class="Datatype Operator">==</a> <a id="8690" href="Library.Bool.html#57" class="InductiveConstructor">false</a>
        <a id="8704" href="Chapter.Imp.HoareLogicSoundness.html#8668" class="Function">b-false</a> <a id="8712" class="Symbol">=</a> <a id="8714" href="Chapter.Imp.HoareLogicSoundness.html#3746" class="Function">lemma-Hoare-loop-exit</a> <a id="8736" href="Chapter.Imp.HoareLogicSoundness.html#8543" class="Bound">hyp3</a>
</pre>
Case `H-While` is the most interesting one. Starting with

          lemma-Hoare-sound {P} {_} {_} {s} {t}
                  (H-While {.P} {b} hyp1) hyp2 hyp3 = ?

and typing `C-c C-l` and then `C-c C-,` with the cursor in the hole we get the context:

          Goal: P t ∧ bval b t == false
          ———————————————————————————————————————————————————————
          hyp3 : ⦅ WHILE b DO c , s ⦆ ⇒ t
          hyp2 : P s
          hyp1 : |- [ (λ s₁ -> P s₁ ∧ bval b s₁ == true) ] c [ P ]

Since the goal is a conjunction, putting the cursor in the hole and typing `C-c C-r` to refine
Agda's guess about the filling of the hole, we get a pair of holes `{!!} , {!!}`; in the first hole
it is expected a proof of `P t`, which is called `Pt` in the above proof, and in the second hole
a proof of `bval b == false` is required, which is called `b-false`.

Now, by passing the induction hypothesis
`lemma-Hoare-sound hyp1 : |= [ (λ s₁ -> P s₁ ∧ bval b s₁ == true) ] c [ P ]` to the lemma
`lemma-Hoare-inv` and then the result to `hyp2` and to `hyp3` we get a proof of the fact
that `P` is an invariant of the command `WHILE b DO c`, hence it holds for the final
state `t` whenever `⦅ WHILE b DO c , s ⦆ ⇒ t`; therefore we have established that `P t`
holds as required.

On the other hand applying `lemma-Hoare-loop-exit` to `hyp3 : ⦅ WHILE b DO c , s ⦆ ⇒ t`
we obtain a proof `b-false : bval b t == false` which ends the proof of this case. 

<pre class="Agda"><a id="10188" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="10206" class="Symbol">{_}</a> <a id="10210" class="Symbol">{_}</a> <a id="10214" class="Symbol">{_}</a> <a id="10218" class="Symbol">{</a><a id="10219" href="Chapter.Imp.HoareLogicSoundness.html#10219" class="Bound">s</a><a id="10220" class="Symbol">}</a> <a id="10222" class="Symbol">{</a><a id="10223" href="Chapter.Imp.HoareLogicSoundness.html#10223" class="Bound">t</a><a id="10224" class="Symbol">}</a>
                               <a id="10257" class="Symbol">(</a><a id="10258" href="Chapter.Imp.HoareLogic.html#4958" class="InductiveConstructor">H-Conseq</a> <a id="10267" href="Chapter.Imp.HoareLogicSoundness.html#10267" class="Bound">x</a> <a id="10269" href="Chapter.Imp.HoareLogicSoundness.html#10269" class="Bound">hyp1</a> <a id="10274" href="Chapter.Imp.HoareLogicSoundness.html#10274" class="Bound">y</a><a id="10275" class="Symbol">)</a> <a id="10277" href="Chapter.Imp.HoareLogicSoundness.html#10277" class="Bound">hyp2</a> <a id="10282" href="Chapter.Imp.HoareLogicSoundness.html#10282" class="Bound">hyp3</a> <a id="10287" class="Symbol">=</a> <a id="10289" href="Chapter.Imp.HoareLogicSoundness.html#10400" class="Function">ths</a>
      <a id="10299" class="Keyword">where</a>

        <a id="10314" href="Chapter.Imp.HoareLogicSoundness.html#10314" class="Function">P₁s</a> <a id="10318" class="Symbol">=</a> <a id="10320" href="Chapter.Imp.HoareLogicSoundness.html#10267" class="Bound">x</a> <a id="10322" href="Chapter.Imp.HoareLogicSoundness.html#10219" class="Bound">s</a> <a id="10324" href="Chapter.Imp.HoareLogicSoundness.html#10277" class="Bound">hyp2</a>
        <a id="10337" href="Chapter.Imp.HoareLogicSoundness.html#10337" class="Function">IH</a>  <a id="10341" class="Symbol">=</a> <a id="10343" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="10361" href="Chapter.Imp.HoareLogicSoundness.html#10269" class="Bound">hyp1</a>
        <a id="10374" href="Chapter.Imp.HoareLogicSoundness.html#10374" class="Function">Q₁t</a> <a id="10378" class="Symbol">=</a> <a id="10380" href="Chapter.Imp.HoareLogicSoundness.html#10337" class="Function">IH</a> <a id="10383" href="Chapter.Imp.HoareLogicSoundness.html#10314" class="Function">P₁s</a> <a id="10387" href="Chapter.Imp.HoareLogicSoundness.html#10282" class="Bound">hyp3</a>
        <a id="10400" href="Chapter.Imp.HoareLogicSoundness.html#10400" class="Function">ths</a> <a id="10404" class="Symbol">=</a> <a id="10406" href="Chapter.Imp.HoareLogicSoundness.html#10274" class="Bound">y</a> <a id="10408" href="Chapter.Imp.HoareLogicSoundness.html#10223" class="Bound">t</a> <a id="10410" href="Chapter.Imp.HoareLogicSoundness.html#10374" class="Function">Q₁t</a>
</pre>In the case `H-Conseq` we have the context:

          Goal: Q t
          ————————————————————————————————————————————————————
          hyp3 : ⦅ c , s ⦆ ⇒ t
          hyp2 : P s
          y    : (s₁ : State) -> Q₁ s₁ -> Q s₁
          hyp1 : |- [ P₁ ] c [ Q₁ ]
          x    : (s₁ : State) -> P s₁ -> P₁ s₁

Then the induction hypothesis `lemma-Hoare-sound hyp1 : |= [ P₁ ] c [ Q₁ ]` can be easily
combined with `P₁s = x s hyp2 : P₁ s` and `Q₁t = IH P₁s hyp3 : Q₁ t` establishing
the thesis `ths = y t Q₁t : Q t` as desired. 

Eventually we conclude: 

<pre class="Agda"><a id="theorem-Hoare-sound"></a><a id="10978" href="Chapter.Imp.HoareLogicSoundness.html#10978" class="Function">theorem-Hoare-sound</a> <a id="10998" class="Symbol">:</a> <a id="11000" class="Symbol">∀</a> <a id="11002" class="Symbol">{</a><a id="11003" href="Chapter.Imp.HoareLogicSoundness.html#11003" class="Bound">P</a> <a id="11005" href="Chapter.Imp.HoareLogicSoundness.html#11005" class="Bound">c</a> <a id="11007" href="Chapter.Imp.HoareLogicSoundness.html#11007" class="Bound">Q</a><a id="11008" class="Symbol">}</a> <a id="11010" class="Symbol">-&gt;</a>
                    <a id="11033" href="Chapter.Imp.HoareLogic.html#4019" class="Datatype Operator">|-</a> <a id="11036" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="11038" href="Chapter.Imp.HoareLogicSoundness.html#11003" class="Bound">P</a> <a id="11040" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="11042" href="Chapter.Imp.HoareLogicSoundness.html#11005" class="Bound">c</a> <a id="11044" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="11046" href="Chapter.Imp.HoareLogicSoundness.html#11007" class="Bound">Q</a> <a id="11048" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="11050" class="Symbol">-&gt;</a> <a id="11053" href="Chapter.Imp.HoareLogicSoundness.html#785" class="Function Operator">|=</a> <a id="11056" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="11058" href="Chapter.Imp.HoareLogicSoundness.html#11003" class="Bound">P</a> <a id="11060" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> <a id="11062" href="Chapter.Imp.HoareLogicSoundness.html#11005" class="Bound">c</a> <a id="11064" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">[</a> <a id="11066" href="Chapter.Imp.HoareLogicSoundness.html#11007" class="Bound">Q</a> <a id="11068" href="Chapter.Imp.HoareLogic.html#2550" class="InductiveConstructor Operator">]</a> 

<a id="11072" href="Chapter.Imp.HoareLogicSoundness.html#10978" class="Function">theorem-Hoare-sound</a> <a id="11092" href="Chapter.Imp.HoareLogicSoundness.html#11092" class="Bound">hyp</a> <a id="11096" class="Symbol">=</a> <a id="11098" href="Chapter.Imp.HoareLogicSoundness.html#5185" class="Function">lemma-Hoare-sound</a> <a id="11116" href="Chapter.Imp.HoareLogicSoundness.html#11092" class="Bound">hyp</a>
</pre>*Remark.* The functions `theorem-Hoare-sound` and `lemma-Hoare-sound` have different definitions,
even if when applied to `hyp` yield the same value. The reason is that these functions
are extensionally equivalent, that is they yield the same values for the same arguments.
However the extensionality principle
is not part of the Agda logic, rather it is just compatible with it and must be postulated for
use in proofs.
 
