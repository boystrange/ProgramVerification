---
title: "Example of derivation with Hoare Logic" 
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Imp.HoareLogicExample where

open import Bool
open import Nat
open import Nat.Properties
open import Logic
open import Logic.Laws
open import Equality
open import Equality.Reasoning
open import LessThan

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

as follows. First we apply rule `H-Loc` twice:

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
represent a property of the state telling how at each iteration it approximates
the final state and hence the result of the whole computation. For this purpose we choose

                                (Z = X + I) ∧ (I ≤ Y)

  

  
```
Plus' : Aexp -> Aexp -> Aexp -> Assn
Plus' a₁ a₂ a₃ = λ s -> (aval a₁ s) == (aval a₂ s) + (aval a₃ s)

Z=X+I : Assn
Z=X+I = Plus' (V Z) (V X) (V I)

-- Loop invariant:  (Z = X + I) ∧ (I ≤ Y)


_<='_ : Aexp -> Aexp -> Assn
a₁ <=' a₂ = λ s -> (aval a₁ s) <= (aval a₂ s)

_<'_ : Aexp -> Aexp -> Assn
a₁ <' a₂ = λ s -> (aval a₁ s) <ℕ (aval a₂ s) == true

sum-prog-inv : Assn
sum-prog-inv = (Plus' (V Z) (V X) (V I)) ∧' ((V I) <=' (V Y))

-- Proof of: |- {(Z = X + I) ∧ (I ≤ Y) ∧ I < Y} sum-prog-body {(Z = X + I) ∧ (I ≤ Y)}

Z+1=X+I+1 : Assn
Z+1=X+I+1 = Plus' (Plus (V Z) (N 1)) (V X) (Plus (V I) (N 1))

Z=X+I+1 : Assn
Z=X+I+1 = Plus' (V Z) (V X) (Plus (V I) (N 1))

I+1<Y+1 : Assn
I+1<Y+1 = (Plus (V I) (N 1)) <' (Plus (V Y) (N 1))

pr2-4 : |- [ Z+1=X+I+1 ∧' I+1<Y+1 ] 
            (Z := Plus (V Z) (N 1))
           [ Z=X+I+1 ∧' I+1<Y+1 ]

pr2-4 = H-Loc {Z=X+I+1 ∧' I+1<Y+1} {Plus (V Z) (N 1)} {Z}

I<=Y : Assn
I<=Y = (V I) <=' (V Y)

I<Y : Assn
I<Y = (V I) <' (V Y)

I<Y+1 : Assn
I<Y+1 = (V I) <' (Plus (V Y) (N 1))

pr2-5 : |- [ Z=X+I+1 ∧' I+1<Y+1 ]
            (I := Plus (V I) (N 1))
           [ Z=X+I ∧' I<Y+1 ]
           
pr2-5 = H-Loc {Z=X+I ∧' I<Y+1} {Plus (V I) (N 1)} {I}

pr2-6 : |- [ Z+1=X+I+1 ∧' I+1<Y+1 ]
            sum-prog-body
           [ Z=X+I ∧' I<Y+1 ]

pr2-6 = H-Comp pr2-4 pr2-5

lemma-<ℕ-< : ∀ {n m : ℕ} -> n <ℕ m == true -> n < m
lemma-<ℕ-< {zero} {succ m} _ = le-succ {0} {m} (le-zero {m})
lemma-<ℕ-< {succ n} {succ m} hyp = le-succ {succ n} {m} IH
  where
    IH : n < m  -- i.e. succ n <= m
    IH = lemma-<ℕ-< {n} {m} hyp

succ-le : ∀ {n m : ℕ} -> succ n <= succ m -> n <= m  -- move to library LessThan
succ-le (le-succ hyp) = hyp

lemma-<-<ℕ : ∀ {n m : ℕ} -> n < m -> n <ℕ m == true
lemma-<-<ℕ {zero} {succ m} hyp = refl
lemma-<-<ℕ {succ n} {succ m} hyp =
           lemma-<-<ℕ {n} {m} (succ-le {succ n} {m} hyp)

lemma-+-1-succ : ∀ n -> n + 1 == succ n
lemma-+-1-succ zero = refl
lemma-+-1-succ (succ n) = cong succ (lemma-+-1-succ n)

impl2-1 : ∀ s -> ∀ {a₁ a₂ : Aexp} -> (a₁ <' Plus a₂ (N 1)) s -> (a₁ <=' a₂) s
impl2-1 s {a₁} {a₂} hyp = ths
  where
    claim : (aval a₁ s) < (aval (Plus a₂ (N 1)) s)
    claim = lemma-<ℕ-< {aval a₁ s} {aval (Plus a₂ (N 1)) s} hyp

    calc : (aval (Plus a₂ (N 1)) s) == succ (aval a₂ s)
    calc = lemma-+-1-succ (aval a₂ s)

    lemma : ∀ {n m p} -> n < m -> m == p -> n < p
    lemma {n} {m} {p} hyp1 hyp2 = subst (λ z -> n < z) hyp2 hyp1

    ths : (aval a₁ s) <= (aval a₂ s)
    ths = succ-le (lemma claim calc)

Z=X+I->Z+1=X+I+1 : ∀ s -> Z=X+I s -> Z+1=X+I+1 s
Z=X+I->Z+1=X+I+1 s hyp = 
    begin
      (aval (V Z) s) + 1           ==⟨ cong (λ z -> z + 1) hyp ⟩       
      (s X + s I) + 1              ==⟨ symm (+-assoc (s X) (s I) 1) ⟩
       s X + (s I + 1)
    end

lt-succ : ∀ {x y : ℕ} -> x < y -> succ x < succ y
lt-succ {x} {y} hyp = le-succ hyp

I<Y->I+1<Y+1 : ∀ s -> I<Y s -> I+1<Y+1 s
I<Y->I+1<Y+1 s hyp = lemma-<-<ℕ {n + 1} {m + 1} c'
  where
    n = aval (V I) s
    m = aval (V Y) s
    
    a' : succ n < succ m
    a' = lt-succ {n} {m} (lemma-<ℕ-< hyp)

    a'' : succ n == n + 1
    a'' = symm (lemma-+-1-succ n)

    b' : n + 1 < succ m
    b' = subst (λ z -> z < succ m) a'' a'

    d' : succ m == m + 1
    d' = symm (lemma-+-1-succ m)

    c' : n + 1 < m + 1
    c' = subst (λ z -> n + 1 < z) d' b'

Z=X+I∧I<=Y∧I<Y->Z+1=X+I+1∧I+1<Y+1 : ∀ s -> ((Z=X+I ∧' I<=Y) ∧' I<Y) s -> (Z+1=X+I+1 ∧' I+1<Y+1) s
Z=X+I∧I<=Y∧I<Y->Z+1=X+I+1∧I+1<Y+1 s ((x , y) , z) = a' , b'
  where
    a' : Z+1=X+I+1 s 
    a' = Z=X+I->Z+1=X+I+1 s x

    b' : I+1<Y+1 s 
    b' = I<Y->I+1<Y+1 s z


lemma-<-+-1-><= : ∀ {n m : ℕ} -> n < m + 1 -> n <= m
lemma-<-+-1-><= {n} {m} hyp = succ-le q
  where
    p : m + 1 == succ m
    p = lemma-+-1-succ m

    q : n < succ m  -- i.e. succ n <= succ m
    q = subst (λ z -> n < z) p hyp


Z=X+I∧I<Y+1->Z=X+I∧I<=Y : ∀ s -> (Z=X+I ∧' I<Y+1) s -> (Z=X+I ∧' I<=Y) s
Z=X+I∧I<Y+1->Z=X+I∧I<=Y s (x , y) = x , h2
  where
    h1 : s I < s Y + 1
    h1 = lemma-<ℕ-< y

    h2 : s I <= s Y
    h2 = lemma-<-+-1-><= h1

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

---------------------------------------------
--            Post-condition
---------------------------------------------


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

--------- Conclusion

-- +-unit-r : (x : ℕ) -> x + 0 == x

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

pr2-3' : |- [ ⊤' ]
           ((Z := V X) :: (I := N 0))
           [ Z=X+I ∧' I<=Y ]

pr2-3' = H-Weak pr2-3 Z=X∧I=0->Z=X+I

pr2-10 : |- [ ⊤' ]
            sum-prog
            [ Z=X+Y ]

pr2-10 = H-Comp pr2-3' pr2-9
```
  
