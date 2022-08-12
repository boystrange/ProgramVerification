---
title: "Arithmetic and boolean expressions"
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.AexpBexp where

open import Bool
open import Nat
open import Nat.Properties
open import Logic
open import Equality
open import Equality.Reasoning

```
-->

In this chapter we introduce the data types `Aexp` and `Bexp` for **arithmetic** and **boolean expressions**
of the language IMP respectively.

Let `{X₀, X₁, ... }` be a denumerable set of **program variables**.
In Agda we formalize `Xᵢ` by `Vn i` namely the variable whose name has pedice or
index `i ∈ Index`, where `Index` is just `ℕ`, the set of natural numbers:

```
Index = ℕ
data Vname : Set where
   Vn : Index → Vname
```

In examples we shall use the following abbreviations:
```
X : Vname
X = Vn 0

Y : Vname
Y = Vn 1

Z : Vname
Z = Vn 2
```

When handling expressions it is often necessary to check whether two variables are the same or not.
For such purpose we define the boolean valued function `x =Vn y` that compares a pair of names `x, y ∈ Vname`,
returning `true` if they are the same, `false` otherwise. Such a definition depends on a similar fanction
`n =ℕ m` checking whether two indexes, namely two natural numbers, are the same:

```
_=ℕ_ : ℕ → ℕ → Bool
zero =ℕ zero = true
zero =ℕ succ m = false
succ n =ℕ zero = false
succ n =ℕ succ m = n =ℕ m

_=Vn_ : (x y : Vname) → Bool
Vn x =Vn Vn y = if x =ℕ y then true else false
```

Now we can define the syntax of arithmetic expressions by the grammar:

                       Aexp ∋ a, a' ::= N n | V vn | Plus a a' 

where `n ∈ Nat`, `vn ∈ Vname`, which is represented by the data type `Aexp`:

```
data Aexp : Set where
   N : ℕ → Aexp                  -- numerals
   V : Vname → Aexp              -- variables
   Plus : Aexp → Aexp → Aexp    -- sum
```

For example the expression `aexp0`:
```
aexp0 : Aexp
aexp0 = Plus (V X) (Plus (N 1) (V Y))
```
is abstract syntax of the (concrete) expression: `X + (1 + Y)`.


### Semantix of aritmetic expressions

The meaning of an expression `a ∈ Aexp` is a value that we define as a natural number. Since `a` may include
program variables we have to assign a meaning to each of them; this is done via the notion of **state**,
which is a mapping from variable names to values:

```
Val = ℕ
State = Vname → Val
```

States are defined as total functions for the sake of simplicity. Indeed to determine the value of an expression
`a` it suffices a partial mapping from the set of variables occurring in `a`, which is obviously finite.
This is consistent with the idea that the state is an abstraction of the finite memory of a computer,
where memory adresses are represented by variable names.

By using the above definition of `State` we avoid dealing with partial functions and the Maybe type constructor
or similar tricks, for example in the subsequent definition of the evaluating function `aval`.

The execution of an imperative program consists of a series of changes of the
meaning of program variables, performed by subsequently **updating** the state, that is a local redefinition
of the meaning of a single variable. We formalize the updating operation by means of the operator
`s [ x ::= v]` returning the state behaving like `s`, but when applied to `x` where it yields `v`.

```
_[_::=_] : State → Vname → Val → State
(s [ x ::= v ]) y = if x =Vn y then v else s y 
```

Then we use the update operation to define states `st1` and `st2` starting with default state `st0`, assigning 0
to all program varibles:

```
st0 : State
st0 = λ x → 0

st1 : State
st1 = st0 [ X ::= 1 ]

st2 : State
st2 = st1 [ Y ::= 2 ]  -- equivalently:  st2 = (st0 [ X ::= 1 ]) [ Y ::= 2 ]
```

The function `aval` is an interpreter of expressions in `Aexp` that uses the state in case of variables:

```
aval : Aexp → State → Val
aval (N n) s = n
aval (V vn) s = s vn
aval (Plus a1 a2) s = aval a1 s + aval a2 s
```

The evaluation of the numeral `N n` does not depend on the state `s`, and just returns n. In case of the
evaluation of a variable `V vn`, `aval` returns the value of the state `s` when applied to `vn` namely `s vn`.
Finally to evaluate `Plus a1 a2` in `s`, `aval` recursively evaluates `a1` and `a2` in the same state `s`, and then
ruturns the sum of the so obtained values, hence by interpreting the symbol `Plus` (a constructor in Agda code)
by the arithmetical function `_+_`.

Consider:

```
example1 : Val
example1 = aval aexp0 st2
```

Then you can check by hitting `C-c C-n example1` that the value of `aexp0` 
encoding the expression `X + (1 + Y)` when computed in the state `st2` above is 4.


### Substitution

**Substitution** is the operation of replacing each occurrence of a variable `x` in an
expression `a` by an expression `a'`, producing the new expression `a [ a' / x]`.

```
_[_/_] : Aexp → Aexp → Vname → Aexp
N n  [ a' / x ] = N n
V y  [ a' / x ] with x =Vn y
... | true  = a'
... | false = V y
Plus a1 a2 [ a' / x ] = Plus (a1 [ a' / x ]) (a2 [ a' / x ])
```

In concrete notation, the substitution `(X + (1 + Y)) [ (Z + 3) / X ]` yields the
expression `(Z + 3) + (1 + Y)`, whose abstract syntax can be obtained
by typing `C-c C-n aexp1` which is defined below:
```
aexp1 : Aexp
aexp1 = aexp0 [ Plus (V Z) (N 3) / X ]
```

Notice that substitution is not recursive:
```
aexp2 : Aexp
aexp2 = aexp0 [ Plus (V X) (N 3) / X ]
```
When typing `C-c Cn aexp2` we get

                     Plus (Plus (V (Vn 0)) (N 3)) (Plus (N 1) (V (Vn 1)))

where rember that `Vn 0 == X`.

### The Substitution lemma

A key property of substitution, which is a syntactic operation, is its consistency with the
semantics of expressions in `Aexp` as given by the evaluation function `aval`. This is some kind
of commutativity property: it tells that by first substituting `a'` for `x` in `a` and
then evaluating the result w.r.t. the state `s` we get the same value as evaluating `a`
in the state `s [ x ::= (aval a' s) ]`, which is `s` where the value of `x` has been updated
to the value of `a'` w.r.t. `s`.

```
lemma-subst-aexp : ∀ (a a' : Aexp) (x : Vname) (s : State) →
                     aval (a [ a' / x ]) s == aval a (s [ x ::= (aval a' s) ])
                     
lemma-subst-aexp (N n) a' x s =
   begin
      aval ((N n) [ a' / x ]) s ==⟨⟩          -- by definition of substitution
      aval (N n) s              ==⟨⟩          -- by definition of aval
      n                         ==⟨⟩          -- by definition of aval
      aval (N n) (s [ x ::= (aval a' s) ])
   end
lemma-subst-aexp (V y) a' x s with x =Vn y
... | true  = refl
... | false = refl
lemma-subst-aexp (Plus a1 a2) a' x s = 
   begin
      aval (a1 [ a' / x ]) s + aval (a2 [ a' / x ]) s  ==⟨ cong2 _+_ h1 h2 ⟩
                                              -- by the ind. hyp. h1, h2
      aval a1 s' + aval a2 s'
   end
   where
      s' : State
      s' =  (s [ x ::= aval a' s ])

      h1 : aval (a1 [ a' / x ]) s == aval a1 (s [ x ::= (aval a' s) ])
      h1 = lemma-subst-aexp a1 a' x s

      h2 : aval (a2 [ a' / x ]) s == aval a2 (s [ x ::= (aval a' s) ])
      h2 = lemma-subst-aexp a2 a' x s
```

Let us spell this proof in more detail. It establishes

                   aval (a [ a' / x ]) s == aval a (s [ x ::= (aval a' s) ])

by induction on `a`.

The case `a == N n` is trivial since `(N n) [ a' / x ] == N n` by substitution definition so that

    aval ((N n) [ a' / x ]) s == aval (N n) s
                              == n
                              == aval (N n) (s [ x ::= (aval a' s) ])

applying twice the definition of `aval`.

Since all these steps are valid by defintion, we use `==⟨⟩` without any justification.
Indeed the proof is verbose, since we could have written just

                   lemma-subst-aexp (N n) a' x s = refl

letting Agda to evaluate the left and right-hand sides of the equation.

The case `a == V y` is rather subtle. A tentative proof would be

                   lemma-subst-aexp (V y) a' x s = if x =Vn y then refl else refl

However the right hand side of it does not type check. The reason is that
the two `refl` in the `if_then_else_` above have different types namely

                   aval a' s == aval a' s    and     s y == s y
           
respectively, while `if_then_else_` has type

                   ∀{A : Set} -> Bool -> A -> A -> A.

We escape the difficulty by means of the `with` construct which is polymorphic.

Finally the case `a == Plus a1 a2` is an immedite consequence of the induction
hypotheses `h1` and `h2`, but these are used inside the
`(a1 [ a' / x ]) s + aval (a2 [ a' / x ]) s`,
for which we have to use the combinator `cong2` from Equality.agda.
The very same proof can be written more concisely by means of the `rewrite` tactic:

    lemma-subst-aexp (Plus a1 a2) a' x s
          rewrite lemma-subst-aexp a1 a' x s | lemma-subst-aexp a2 a' x s = refl

## Boolean expressions

The syntax of bolean expressions is defined by the grammar:

                   Bexp ∋ b, b' ::= B bc | Leq a a' | Not b | And b b'

where `bc ∈ Bool` and `a, a' ∈ Aexp`.

```
data Bexp : Set where
   B : Bool → Bexp             -- boolean constants
   Leq : Aexp → Aexp → Bexp    -- less than
   Not : Bexp → Bexp           -- negation
   And : Bexp → Bexp → Bexp    -- conjunction
```

The semantics of expressions in Bexp associate a boolean value is a boolean; in particular
the meaning of `Leq a a'` is `aval a s < aval a's`, therefore in general the meaning of `b ∈ Bexp`
must depend on a state `s`.

```
_<ℕ_ : ℕ → ℕ → Bool          --  n <ℕ m == true if n < m 
zero <ℕ   zero   = false     --  in the ordinary ordering of ℕ
zero <ℕ   succ n = true
succ n <ℕ zero   = false
succ n <ℕ succ m = n <ℕ m

bval : Bexp → State → Bool
bval (B x) s       = x
bval (Leq x y) s   = (aval x s) <ℕ (aval y s)
bval (Not b) s     = not (bval b s)
bval (And b1 b2) s = bval b1 s && bval b2 s
```

## Exercises

1. Prove that the function bval is total, namely that

   lemma-bval-tot : ∀ (b : Bexp) (s : State) → bval b s == true ∨ bval b s == false
   
2. Define a suitable function  `_[_/_]B :  Bexp → Aexp → Vname → Bexp` extending
   substitution to expressions in `Bexp` and prove the lemma:

               lemma-subst-bexp : ∀(b : Bexp) (a : Aexp) (x : Vname) (s : State) →
                           bval (b [ a / x ]B) s == bval b (s [ x ::= aval a s ])
                


```
-- EXERCISE 1

lemma-bval-tot : ∀ (b : Bexp) (s : State) → bval b s == true ∨ bval b s == false
lemma-bval-tot b s with bval b s
... | true  = inl refl
... | false = inr refl

--EXERCISE 2

_[_/_]B : Bexp → Aexp → Vname → Bexp
B c [ a / x ]B       = B c
Leq a1 a2 [ a / x ]B = Leq (a1 [ a / x ]) (a2 [ a / x ])
Not b [ a / x ]B     = Not (b [ a / x ]B)
And b1 b2 [ a / x ]B = And (b1 [ a / x ]B) (b2 [ a / x ]B)

lemma-subst-bexp : ∀(b : Bexp) (a : Aexp) (x : Vname) (s : State) →
                     bval (b [ a / x ]B) s == bval b (s [ x ::= aval a s ])
                     
lemma-subst-bexp (B c) a x s = refl
lemma-subst-bexp (Leq a1 a2) a x s =
    begin
       bval (Leq a1 a2 [ a / x ]B) s                        ==⟨⟩
       bval (Leq (a1 [ a / x ]) (a2 [ a / x ])) s           ==⟨⟩
       (aval  (a1 [ a / x ]) s) <ℕ (aval  (a2 [ a / x ]) s) ==⟨ cong2 _<ℕ_ lemma1 lemma2 ⟩
       (aval a1 s') <ℕ (aval a2 s')                         ==⟨⟩
       bval (Leq a1 a2) s'
    end
    where
         s' : State
         s' = s [ x ::= aval a s ]

         lemma1 : aval (a1 [ a / x ]) s == aval a1 (s [ x ::= aval a s ])
         lemma1 = lemma-subst-aexp a1 a x s

         lemma2 : aval (a2 [ a / x ]) s == aval a2 (s [ x ::= aval a s ])
         lemma2 = lemma-subst-aexp a2 a x s
lemma-subst-bexp (Not b) a x s
         rewrite lemma-subst-bexp b a x s = refl
lemma-subst-bexp (And b1 b2) a x s
         rewrite lemma-subst-bexp b1 a x s | lemma-subst-bexp b2 a x s = refl
```
{:.solution}
