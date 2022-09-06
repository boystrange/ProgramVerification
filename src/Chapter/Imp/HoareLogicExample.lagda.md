---
title: "Example of derivation with Hoare Logic" 
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Imp.HoareLogicExample where

open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Logic.Laws
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.LessThan

open import Chapter.Imp.AexpBexp
open import Chapter.Imp.BigStep
open import Chapter.Imp.HoareLogic

```
-->

Consider the program `sum-prog` computing the sum of two natural numbers by iterating the successor:
 
    Z := X ;
    I := 0 ;
    WHILE I < Y DO
          Z := Z + 1 ;
          I := I + 1

Then we want to show that 

    |- {⊤} sum-prog {Z = X + Y}


To begin with, we encode the program into the IMP syntax:
```
I : Vname
I = Vn 3

-- Initialization: Z := X ; I := 0

sum-prog-init : Com
sum-prog-init = (Z := V X) :: (I := N 0)

-- Body:           Z := Z + 1 ; I := I + 1

sum-prog-body : Com
sum-prog-body = (Z := (Plus (V Z) (N 1))) ::
                (I := (Plus (V I) (N 1)))

-- Complete program computing X + Y by iterating the successor

sum-prog : Com
sum-prog = sum-prog-init ::
           (WHILE (Less (V I) (V Y)) DO
                 sum-prog-body)

```


### Initialization

To improve readability, we introduce the following abbreviations of assertions:

```
X=X : Assn
X=X =  (V X ==' V X)

0=0 : Assn
0=0 = (N 0 ==' N 0)

Z=X : Assn
Z=X = (V Z ==' V X)

I=0 : Assn
I=0 = (V I ==' N 0)
```
Then we prove

           [ X=X ∧' 0=0 ]
           (Z := V X) :: (I := N 0)
           [ Z=X ∧' I=0 ]

First, we apply rule `H-Loc` twice:

```
pr2-0 : |- [ X=X ∧' 0=0 ]
           (Z := V X)
           [ Z=X ∧' 0=0 ]
           
pr2-0 = H-Loc {Z=X ∧' 0=0} {V X} {Z}

pr2-1 : |- [ Z=X ∧' 0=0 ]
           (I := N 0)
           [ Z=X ∧' I=0 ]
           
pr2-1 = H-Loc {Z=X ∧' I=0} {N 0} {I}
```
Then we combine these proofs using rule `H-Comp`:
```
pr2-2 : |- [ X=X ∧' 0=0 ]
           (Z := V X) :: (I := N 0)
           [ Z=X ∧' I=0 ]

pr2-2 = H-Comp pr2-0 pr2-1
```
Since the pre-condition `X=X ∧' 0=0` is trivially true of any state,
it is a logical consequence of the trivial assertion `⊤'`:
```
⊤->X=X∧I=0 : ∀ s -> ⊤' s -> (X=X ∧' 0=0) s
⊤->X=X∧I=0 _ _ = refl , refl
```
Combining this implication with the proof `pr2-2`, by rule `H-Str` we get: 
```
pr2-3 : |- [ ⊤' ]
           (Z := V X) :: (I := N 0)
           [ Z=X ∧' I=0 ]

pr2-3 = H-Str ⊤->X=X∧I=0 pr2-2
```

### Loop

The central part of the proof is devising the appropriate **loop-invariant**; it should
represent a property of the state telling how it approximates 
the final state  at each iteration and hence the result of the whole computation.
For this purpose we choose

    (Z = X + I) ∧ (I ≤ Y) 

To encode this assertion, as well as the others that will be involved in the proof, 
we introduce three new predicates:
  
```
Plus' : Aexp -> Aexp -> Aexp -> Assn
Plus' a₁ a₂ a₃ = λ s -> (aval a₁ s) == (aval a₂ s) + (aval a₃ s)

_<='_ : Aexp -> Aexp -> Assn
a₁ <=' a₂ = λ s -> (aval a₁ s) <= (aval a₂ s)

_<'_ : Aexp -> Aexp -> Assn
a₁ <' a₂ = λ s -> (aval a₁ s) <ℕ (aval a₂ s) == true
```
Then we define: 
```
Z=X+I : Assn
Z=X+I = Plus' (V Z) (V X) (V I)

I<=Y : Assn
I<=Y = (V I) <=' (V Y)
```
Now, the invariant can be written as follows:
```
sum-prog-inv : Assn
sum-prog-inv = Z=X+I ∧' I<=Y
```
The next step is to show that 

    |- [ (Z=X+I ∧' I<=Y) ∧' I<Y ]
         (Z := (Plus (V Z) (N 1))) ::
         (I := (Plus (V I) (N 1)))
       [ (Z=X+I ∧' I<=Y) ]

where 
```
I<Y : Assn
I<Y = (V I) <' (V Y)
```
Toward such proof, we first introduce some abbreviations:
```
Z+1=X+I+1 : Assn
Z+1=X+I+1 = Plus' (Plus (V Z) (N 1)) (V X) (Plus (V I) (N 1))

Z=X+I+1 : Assn
Z=X+I+1 = Plus' (V Z) (V X) (Plus (V I) (N 1))

I+1<Y+1 : Assn
I+1<Y+1 = (Plus (V I) (N 1)) <' (Plus (V Y) (N 1))

I<Y+1 : Assn
I<Y+1 = (V I) <' (Plus (V Y) (N 1))
```
Then we establish the proof below concerning the body:
```
pr2-4 : |- [ Z+1=X+I+1 ∧' I+1<Y+1 ] 
            (Z := Plus (V Z) (N 1))
           [ Z=X+I+1 ∧' I+1<Y+1 ]

pr2-4 = H-Loc {Z=X+I+1 ∧' I+1<Y+1} {Plus (V Z) (N 1)} {Z}


pr2-5 : |- [ Z=X+I+1 ∧' I+1<Y+1 ]
            (I := Plus (V I) (N 1))
           [ Z=X+I ∧' I<Y+1 ]
           
pr2-5 = H-Loc {Z=X+I ∧' I<Y+1} {Plus (V I) (N 1)} {I}

pr2-6 : |- [ Z+1=X+I+1 ∧' I+1<Y+1 ]
            sum-prog-body
           [ Z=X+I ∧' I<Y+1 ]

pr2-6 = H-Comp pr2-4 pr2-5
```
To use `pr2-6` when proving that `Z=X+I ∧' I<=Y` is a loop-invariant
we have to establish the implications:

            (Z=X+I ∧' I<=Y) ∧' I<Y ==> Z+1=X+I+1 ∧' I+1<Y+1    and

            Z=X+I ∧' I<Y+1 ==> Z=X+I ∧' I<=Y

Before facing such task and for further use in the proof, we establish some
lemmas about the properties of `<=` and `<`:
```
succ-le : ∀ {n m : ℕ} -> succ n <= succ m -> n <= m  -- move to library LessThan
succ-le (le-succ hyp) = hyp

+-1-succ : ∀ n -> n + 1 == succ n
+-1-succ zero = refl
+-1-succ (succ n) = cong succ (+-1-succ n)

lt-succ : ∀ {x y : ℕ} -> x < y -> succ x < succ y
lt-succ {x} {y} hyp = le-succ hyp

lemma-<-+-1-><= : ∀ {n m : ℕ} -> n < m + 1 -> n <= m
lemma-<-+-1-><= {n} {m} hyp = succ-le q
  where
    p : m + 1 == succ m
    p = +-1-succ m

    q : n < succ m  -- i.e. succ n <= succ m
    q = subst (λ z -> n < z) p hyp
```
Also, we have to establish that the predicate `n < m` is equivalent to
`n <ℕ m  == true`:
```
lemma-<ℕ-< : ∀ {n m : ℕ} -> n <ℕ m == true -> n < m
lemma-<ℕ-< {zero} {succ m} _ = le-succ {0} {m} (le-zero {m})
lemma-<ℕ-< {succ n} {succ m} hyp = le-succ {succ n} {m} IH
  where
    IH : n < m  -- i.e. succ n <= m
    IH = lemma-<ℕ-< {n} {m} hyp

lemma-<-<ℕ : ∀ {n m : ℕ} -> n < m -> n <ℕ m == true
lemma-<-<ℕ {zero} {succ m} hyp = refl
lemma-<-<ℕ {succ n} {succ m} hyp =
           lemma-<-<ℕ {n} {m} (succ-le {succ n} {m} hyp)
```
Now, we are in place to prove the required implications:
```
Z=X+I->Z+1=X+I+1 : ∀ s -> Z=X+I s -> Z+1=X+I+1 s
Z=X+I->Z+1=X+I+1 s hyp = 
    begin
      (aval (V Z) s) + 1           ==⟨ cong (λ z -> z + 1) hyp ⟩       
      (s X + s I) + 1              ==⟨ symm (+-assoc (s X) (s I) 1) ⟩
       s X + (s I + 1)
    end
    
I<Y->I+1<Y+1 : ∀ s -> I<Y s -> I+1<Y+1 s
I<Y->I+1<Y+1 s hyp = lemma-<-<ℕ {n + 1} {m + 1} c'
  where
    n = aval (V I) s
    m = aval (V Y) s
    
    a' : succ n < succ m
    a' = lt-succ {n} {m} (lemma-<ℕ-< hyp)

    a'' : succ n == n + 1
    a'' = symm (+-1-succ n)

    b' : n + 1 < succ m
    b' = subst (λ z -> z < succ m) a'' a'

    d' : succ m == m + 1
    d' = symm (+-1-succ m)

    c' : n + 1 < m + 1
    c' = subst (λ z -> n + 1 < z) d' b'

Z=X+I∧I<=Y∧I<Y->Z+1=X+I+1∧I+1<Y+1 :
       ∀ s -> ((Z=X+I ∧' I<=Y) ∧' I<Y) s -> (Z+1=X+I+1 ∧' I+1<Y+1) s
       
Z=X+I∧I<=Y∧I<Y->Z+1=X+I+1∧I+1<Y+1 s ((x , y) , z) = a' , b'
  where
    a' : Z+1=X+I+1 s 
    a' = Z=X+I->Z+1=X+I+1 s x

    b' : I+1<Y+1 s 
    b' = I<Y->I+1<Y+1 s z

Z=X+I∧I<Y+1->Z=X+I∧I<=Y : ∀ s -> (Z=X+I ∧' I<Y+1) s -> (Z=X+I ∧' I<=Y) s
Z=X+I∧I<Y+1->Z=X+I∧I<=Y s (x , y) = x , h2
  where
    h1 : s I < s Y + 1
    h1 = lemma-<ℕ-< y

    h2 : s I <= s Y
    h2 = lemma-<-+-1-><= h1
```
Putting al togather, we obtain: 
```
pr2-7 : |- [ (Z=X+I ∧' I<=Y) ∧' I<Y ]
            sum-prog-body
           [ (Z=X+I ∧' I<=Y) ]
           
pr2-7 = H-Conseq Z=X+I∧I<=Y∧I<Y->Z+1=X+I+1∧I+1<Y+1
                 pr2-6
                 Z=X+I∧I<Y+1->Z=X+I∧I<=Y

¬I<Y : Assn
¬I<Y = λ s -> s I <ℕ s Y == false

pr2-8 : |- [ Z=X+I ∧' I<=Y ]
            (WHILE (Less (V I) (V Y)) DO
                 sum-prog-body)
            [ (Z=X+I ∧' I<=Y) ∧' ¬I<Y ]

pr2-8 = H-While pr2-7
```
In summary we have proved

    pr2-3 : |- [ ⊤' ]
           (Z := V X) :: (I := N 0)
           [ Z=X ∧' I=0 ]

    and

    pr2-8 : |- [ Z=X+I ∧' I<=Y ]
            (WHILE (Less (V I) (V Y)) DO
                 sum-prog-body)
            [ (Z=X+I ∧' I<=Y) ∧' ¬I<Y ]


It remains to show that

    Z=X ∧' I=0 ==> Z=X+I ∧' I<=Y

to link `pr2-3` and `pr2-8`
```
Z=X∧I=0->Z=X+I : ∀ s -> (Z=X ∧' I=0) s -> (Z=X+I ∧' I<=Y) s
Z=X∧I=0->Z=X+I s (x , y) = eq1 , eq2
  where

    eq1 : s Z == s X + s I
    eq1 = begin
             s Z          ==⟨ x ⟩
             s X          ==⟨ symm (+-unit-r (s X)) ⟩
             s X + 0      ==⟨ cong (λ z -> s X + z) (symm y) ⟩
             s X + s I
          end

    eq2 : s I <= s Y
    eq2 = subst (λ z -> z <= s Y) (symm y) (le-zero {s Y})

```
and to show that 

    (Z=X+I ∧' I<=Y) ∧' ¬I<Y ==> Z=X+Y

to get the desired post-condition
```
leq-not-le :  ∀ (n m : ℕ) -> n <= m -> n <ℕ m == false -> n == m

leq-not-le zero zero hyp1 hyp2 = refl
leq-not-le (succ n) (succ m ) (le-succ hyp1) hyp2 =
                             cong succ (leq-not-le n m hyp1 hyp2)

leq-not-le' : ∀(a a' : Aexp) (s : State)
            -> (a <=' a') s -- aval a s <= aval a' s
            -> bval (Less a a') s == false
            -> (a ==' a') s -- aval a s == aval a' s
            
leq-not-le' a a' s hyp1 hyp2 =
            leq-not-le (aval a s) (aval a' s) hyp1 hyp2

Z=X+Y : Assn
Z=X+Y = Plus' (V Z) (V X) (V Y)

Z=X+I∧I<=Y∧¬I<Y->Z=X+Y : ∀ s -> ((Z=X+I ∧' I<=Y) ∧' ¬I<Y) s -> Z=X+Y s
Z=X+I∧I<=Y∧¬I<Y->Z=X+Y s ((x , y) , z) = ths
  where
    eq : s I == s Y 
    eq = leq-not-le' (V I) (V Y) s y z

    ths : Z=X+Y s
    ths = subst (λ z -> s Z == s X + z) eq x

pr2-9 : |- [ Z=X+I ∧' I<=Y ]
            (WHILE (Less (V I) (V Y)) DO
                 sum-prog-body)
            [ Z=X+Y ]
            
pr2-9 = H-While' pr2-7 Z=X+I∧I<=Y∧¬I<Y->Z=X+Y
```
Eventually we put all togather: 
```
pr2-3' : |- [ ⊤' ]
           ((Z := V X) :: (I := N 0))
           [ Z=X+I ∧' I<=Y ]

pr2-3' = H-Weak pr2-3 Z=X∧I=0->Z=X+I

pr2-10 : |- [ ⊤' ]
            sum-prog
            [ Z=X+Y ]

pr2-10 = H-Comp pr2-3' pr2-9
```
  
