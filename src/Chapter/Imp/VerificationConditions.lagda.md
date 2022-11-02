---
title: "Verification Conditions"
prev:  Chapter.Imp.HoareLogicCompleteness 
---
  
```
module Chapter.Imp.VerificationConditions where
```
 
## Imports 

```
open import Library.Bool
open import Library.Nat
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Chapter.Imp.AexpBexp
open import Chapter.Imp.BigStep
open import Chapter.Imp.HoareLogic

```
 
The verification of the program `sum-prog` in chapter
[Example of derivation with Hoare logic]({% link pages/Chapter.Imp.HoareLogicExample.md %})
makes it apparent how difficult may be to directly use Hoare logic for program verification without the help
of some mechanical procedure. From a quick insepection of that proof one realizes that most of the effort
resides in establishing rather obvious implications among assertions occurring in the rule `H-Conseq` or its
variants. At least in this example, these consist of simple facts from arithmetic, involving sum and order,
stated using quantifier-free formulas; but such formulas could be proved authomatically using e.g. tools
based on satisfiability-modulo-theories, SMT.

To make such a remark effective, it would be of great advantage to factor the arithmetic part of the proofs
out of the remaining inferences using other rules of Hoare logic. In fact, the latters essentially follow the
structure of the program and seem to be computable starting with the post-condition. This is suggested by the
the main properties of the predicate `wp` in chapter
[Relative Completeness of Hoare logic]({% link pages/Chapter.Imp.HoareLogicCompleteness.md %}), namely

     Fact : ∀ {P c Q} -> |= [ P ] c [ Q ] -> (∀ s -> P s -> wp c Q s)
     wp-lemma : ∀ c {Q : Assn} -> |- [ wp c Q ] c [ Q ]

Indeed, suppose that we have to verify the program `c` against the pre-condition `P` and post-condition `Q`; this
amounts to prove that `|= [ P ] c [ Q ]` which by the
[soundness of Hoare logic]({% link pages/Chapter.Imp.HoareLogicSoundness.md %})
is consequence of the derivability of `|- [ P ] c [ Q ]`. By computing `wp c Q` we have
that `∀ s -> P s -> wp c Q s` by `Fact` and `|- [ wp c Q ] c [ Q ]` by the `wp-lemma`,
from which the desired proof of `|- [ P ] c [ Q ]` follows by rule `H-Str`:

          ∀ s -> P s -> wp c Q s     |- [ wp c Q ] c [ Q ]
    H-Str ------------------------------------------------
                       |- [ P ] c [ Q ]

However the definition of `wp` is semantic, while we need a syntactic definition to compute the weakest precondition
`wp c Q`. Let us try to define `wp c Q` by induction over the command `c`. The first cases are rather obvious:

    wp SKIP     Q s = Q s
    wp (x := a) Q s = Q (s [ x ::= aval a s ])

From the proof of lemma `wp-lemma` in case of the command `c₁ :: c₂` we see that we can define:

    wp (c₁ :: c₂) Q s = wp c₁ (wp c₂ Q) s 

The case of `IF` command is easy:
                                    
    wp (IF b THEN c₁ ELSE c₂) Q s = wp c₁ Q s     if aval b s == true
                                  = wp c₂ Q s     if aval b s == false
 
Where the attempt fails is in case of a `WHILE` command. Indeed, by exploting the equivalence 

    (WHILE b DO c) ∼ (IF b THEN (c :: (WHILE b DO c)) ELSE SKIP)

(see chapter [Big-step operational semantics]({% link pages/Chapter.Imp.BigStep.md %}), exercise 3) we could set

    pre (WHILE b DO c) Q s = wp (c :: (WHILE b DO c)) Q s    if bval b s == true
                           = Q s                             if bval b s == false

so that in case `bval b s == true` we have 

    wp (c :: (WHILE b DO c)) Q s = wp c (wp (WHILE b DO c) Q) s

But then the definition of `pre (WHILE b DO c) Q` depends on itself. 
 
 
## Verification conditions
 
Let us look at the rule `H-While`:

             |- [ (λ s -> P s ∧ bval b s == true) ] c [ P ]
     H-While ------------------------------------------------------------
             |- [ P ] (WHILE b DO c) [ (λ s -> P s ∧ bval b s == false) ]
     
Then the pre-condition `P` in the conclusion is the invariant assertion of the command `WHILE b DO c` and it is the
desired `wp (WHILE b DO c) Q` provided that `P s ∧ bval b s == false` implies `Q s` for all `s`.

Now, a way out of the impasse in the inductive definition of `wp` in case of the `WHILE` command is to ask
the user to provide
herself an invariant `I` for each loop in her program, and then to verify that such `I`'s are the
correct choice by generating a formula expressing that they are actual invariants of the
respective `WHILE` commands: these are the *verification conditions*.

We begin by defining the grammar of *annotated commands*, namely IMP commands where each `WHILE` command
carries a (candidate) invariant assertion.
 
```
data Acom : Set₁ where
  SKIP  :  Acom
  _:=_  :  Vname → Aexp → Acom           
  _::_  :  Acom → Acom → Acom   
  IF_THEN_ELSE_ : Bexp → Acom → Acom → Acom 
  WHILE[_]_DO_  : Assn → Bexp → Acom → Acom

```
To recover the IMP command corresponding to `C : Acom` there is an obvious erasure map called `strip`: 

```
strip : Acom → Com
strip SKIP = SKIP
strip (x := a) = x := a
strip (C₁ :: C₂) = strip C₁ :: strip C₂
strip (IF b THEN C₁ ELSE C₂) = IF b THEN strip C₁ ELSE strip C₂
strip (WHILE[ I ] b DO C) = WHILE b DO strip C

```
Inspired to the tentative syntactic definition of `wp`, we define the assertion `pre C Q` as follows:

```
pre : Acom → Assn → Assn
pre SKIP Q = Q
pre (x := a) Q s =  Q (s [ x ::= aval a s ])
pre (C₁ :: C₂) Q = pre C₁ (pre C₂ Q)
pre (IF b THEN C₁ ELSE C₂) Q s with bval b s
...   | true  = pre C₁ Q s
...   | false = pre C₂ Q s
pre (WHILE[ I ] b DO C) Q = I

```
Then, given an annotated command `C : Acom` and the post-condition `Q`,
we define the verification condition `vc C Q` asserting that all the invariants
`I` occurring in some subexpression `WHILE[ I ] b DO C'` of `C` are actual invariants
of the command `WHILE b DO (strip C')`, so that `pre C Q` can be regarded as a valid
pre-condition of the command `strip C` with respect to the post-condition `Q`: 

```
vc : Acom → Assn → Set
vc SKIP Q = ⊤
vc (x := a) Q = ⊤
vc (C₁ :: C₂) Q = vc C₁ (pre C₂ Q) ∧ vc C₂ Q
vc (IF b THEN C₁ ELSE C₂) Q = vc C₁ Q ∧ vc C₂ Q
vc (WHILE[ I ] b DO C) Q =
   (∀ s → I s ∧ bval b s == true → pre C I s) ∧
   (∀ s → I s ∧ bval b s == false → Q s) ∧
   vc C I
```

Now, we have to prove that if the verification condition `vc C Q` is satisfied then we can derive
`|- [ pre C Q ] strip C [ Q ]` in Hoare logic, and hence `|= [ pre C Q ] strip C [ Q ]`, namely
the triple `[ pre C Q ] strip C [ Q ]` is valid. 

```
vc-sound : ∀ {Q : Assn} C → vc C Q → |- [ pre C Q ] strip C [ Q ]
vc-sound SKIP hyp = H-Skip
vc-sound (x := a) hyp = H-Loc
vc-sound {Q} (C₁ :: C₂) (hyp1 , hyp2) = H-Comp IH1 IH2
  where
    IH1 : |- [ pre C₁ (pre C₂ Q) ] strip C₁ [ pre C₂ Q ]
    IH1 = vc-sound C₁ hyp1

    IH2 : |- [ pre C₂ Q ] strip C₂ [ Q ]
    IH2 = vc-sound C₂ hyp2

vc-sound {Q} (IF b THEN C₁ ELSE C₂) (hyp1 , hyp2) = H-If if-True if-False
  where
    IH1 : |- [ pre C₁ Q ] strip C₁ [ Q ]
    IH1 = vc-sound C₁ hyp1

    case-True : ∀ s → pre (IF b THEN C₁ ELSE C₂) Q s ∧ bval b s == true → pre C₁ Q s
    case-True s (hyp3 , hyp4) rewrite hyp4 = hyp3
    
    -- hyp4 : bval b s == true
    -- hyp3 : pre (IF b THEN c₁ ELSE c₂) Q s | bval b s

    if-True : |- [ (λ s → pre (IF b THEN C₁ ELSE C₂) Q s ∧ bval b s == true) ] strip C₁ [ Q ]
    if-True = H-Str case-True IH1

    IH2 : |- [ pre C₂ Q ] strip C₂ [ Q ]
    IH2 = vc-sound C₂ hyp2

    case-False : ∀ s → pre (IF b THEN C₁ ELSE C₂) Q s ∧ bval b s == false → pre C₂ Q s
    case-False s (hyp5 , hyp6) rewrite hyp6 = hyp5
    
    -- hyp6 : bval b s == false
    -- hyp5 : pre (IF b THEN C₁ ELSE C₂) Q s | bval b s

    if-False : |- [ (λ s → pre (IF b THEN C₁ ELSE C₂) Q s ∧ bval b s == false) ] strip C₂ [ Q ]
    if-False = H-Str case-False IH2

vc-sound {Q} (WHILE[ I ] b DO C) (hyp7 , hyp8 , hyp9) = H-Weak While-conclusion hyp8

  -- hyp7 : ∀ s → I s ∧ bval b s == true → pre C I s
  -- hyp8 : ∀ s → I s ∧ bval b s == false → Q s
  -- hyp9 : vc C I
  
  where
    IH : |- [ pre C I ] strip C [ I ]
    IH = vc-sound C hyp9

    While-premise : |- [ (λ s → I s ∧ bval b s == true) ] strip C [ I ]
    While-premise = H-Str hyp7 IH

    While-conclusion : |- [ I ] WHILE b DO (strip C) [ (λ s → I s ∧ bval b s == false) ]
    While-conclusion = H-While While-premise
```

## Completeness of the verification conditions method 

Should it be the case that `|- [ pre C Q ] strip C [ Q ]` implies that `vc C Q` is valid? The answer is obviously
not; indeed this would be clearly false if the invariants in `C` are ill choosen, say because they are just trivial
assertions like `⊤'`. However it is true that any proof of `|- [ P ] c [ Q ]` implicitly includes its own
verification condition, so that we can show that for any such triple there exists a properly annotated
command `C` such that `c == strip C`, the assertion `vc C Q` is valid and `P` implies `pre C Q`.

Toward the proof of such a theorem, we prove two lemmas stating that if `P` implies `P'` then
both `pre C P` implies `pre C P'` and `vc C P` implies `vc C P'`. 

```
pre-mono : ∀{P P' : Assn} {s : State} (C : Acom)
           → (∀ s' → P s' → P' s') → pre C P s → pre C P' s
           
pre-mono {s = s''} SKIP hyp1 hyp2 = hyp1 s'' hyp2
-- {s = s''} is short for {P} {P'} {s''} where just the binding of s to s'' matters
pre-mono {s = s''} (x := a) hyp1 hyp2 = hyp1 (s'' [ x ::= aval a s'' ]) hyp2
pre-mono {P} {P'} {s} (C₁ :: C₂) hyp1 hyp2 = thesis
  
  -- hyp1 : ∀ s' → P s' → P' s'
  -- hyp2 : pre C₁ (pre C₂ P) s
  
  where
    pre-C₂ : ∀ s → pre C₂ P s → pre C₂ P' s
    pre-C₂ s = pre-mono C₂ hyp1

    thesis : pre C₁ (pre C₂ P') s
    thesis = pre-mono C₁ pre-C₂ hyp2

pre-mono {s = s} (IF b THEN C₁ ELSE C₂) hyp1 hyp2 
  -- hyp1 : ∀ s' → P s' → P' s'
  -- hyp2 : pre (IF b THEN C₁ ELSE C₂) P s | bval b s
  with bval b s
... | true  = pre-mono C₁ hyp1 hyp2
... | false = pre-mono C₂ hyp1 hyp2

pre-mono (WHILE[ I ] b DO C) hyp1 hyp2 = hyp2
  -- hyp1 : ∀ s' → P s' → P' s'
  -- hyp2 : I s


vc-mono : ∀ {P P' : Assn} (C : Acom) →
               (∀ s -> P s → P' s) → vc C P → vc C P'

vc-mono SKIP hyp1 hyp2 = hyp2

vc-mono (x := a) hyp1 hyp2 = hyp2

vc-mono {P} {P'} (C₁ :: C₂) hyp1 (hyp2 , hyp3) = IH1 , IH2
  -- hyp1 : ∀ s → P s → P' s
  -- hyp2 : vc C₁ (pre C₂ P)
  -- hyp3 : vc C₂ P
  where
    pre-C₂ : (∀ s → pre C₂ P s → pre C₂ P' s)
    pre-C₂ = λ _ → pre-mono C₂ hyp1            -- λ _ is dummy for λ (s : State)

    IH1 : vc C₁ (pre C₂ P')
    IH1 = vc-mono C₁ pre-C₂ hyp2

    IH2 : vc C₂ P'
    IH2 = vc-mono C₂ hyp1 hyp3
vc-mono {P} {P'} (IF b THEN C₁ ELSE C₂) hyp (hyp1 , hyp2) = IH1 , IH2
    -- hyp  : ∀ s → P s → P' s
    -- hyp1 : vc C₁ P
    -- hyp2 : vc C₂ P
    where
      IH1 : vc C₁ P'
      IH1 = vc-mono C₁ hyp hyp1

      IH2 : vc C₂ P'
      IH2 = vc-mono C₂ hyp hyp2
    
vc-mono {P} {P'} (WHILE[ I ] b DO C) hyp (hyp1 , hyp2 , hyp3) = th1 , th2 , th3
    -- hyp  : ∀ s → P s → P' s
    -- hyp1 : ∀ s → I s ∧ bval b s == true → pre C I s
    -- hyp2 : ∀ s → I s ∧ bval b s == false → P s
    -- hyp3 : vc C I
    where
      th1 : ∀ s → I s ∧ bval b s == true → pre C I s
      th1 = hyp1

      th2 : ∀ s → I s ∧ bval b s == false → P' s
      th2 s h = hyp s (hyp2 s h)

      th3 : vc C I
      th3 = hyp3


```

We are now in place to prove the completeness theorem of verification conditions by induction
over the derivation of `|- [ P ] c [ Q ]`. 

```
vc-completeness : ∀ {P Q : Assn} c →
            |- [ P ] c [ Q ] →
            ∃[ C ] ( c == strip C ∧ vc C Q ∧ (∀ s → P s → pre C Q s) )

vc-completeness SKIP H-Skip = SKIP , refl , (<> , (λ s h → h))
vc-completeness (x := a) H-Loc = (x := a) , (refl , (<> , λ s h → h))
vc-completeness (c₁ :: c₂) (H-Comp {P = P} {R} {Q} hyp₁ hyp₂) =
                (C₁ :: C₂) , (A , D , h)
                
  -- hyp₁ : |- [ P ] c₁ [ R ]
  -- hyp₂ : |- [ R ] c₂ [ Q ]

  where
    IH₁ : ∃[ C₁ ] ( c₁ == strip C₁ ∧ vc C₁ R ∧ (∀ s → P s → pre C₁ R s) )
    IH₁ = vc-completeness {P} {R} c₁ hyp₁

    IH₂ : ∃[ C₂ ] ( c₂ == strip C₂ ∧ vc C₂ Q ∧ (∀ s → R s → pre C₂ Q s) )
    IH₂ = vc-completeness {R} {Q} c₂ hyp₂
  
    C₁ : Acom
    C₁ = fst IH₁

    C₂ : Acom
    C₂ = fst IH₂

    Matr₁ : c₁ == strip C₁ ∧ vc C₁ R ∧ (∀ s → P s → pre C₁ R s)
    Matr₁ = snd IH₁

    Matr₂ : c₂ == strip C₂ ∧ vc C₂ Q ∧ (∀ s → R s → pre C₂ Q s)
    Matr₂ = snd IH₂

    A : (c₁ :: c₂) == strip (C₁ :: C₂)
    A = begin c₁ :: c₂             ==⟨ cong (λ z → z :: c₂)       (fst Matr₁) ⟩
              strip C₁ :: c₂       ==⟨ cong (λ z → strip C₁ :: z) (fst Matr₂) ⟩
              strip C₁ :: strip C₂
        end

    D : vc (C₁ :: C₂) Q  -- vc C₁ (pre C₂ Q) ∧ vc C₂ Q
    D = vc-mono C₁ (snd (snd Matr₂)) (fst (snd Matr₁)) ,
        fst (snd Matr₂)

    f : ∀ s → P s → pre C₁ R s
    f = snd (snd Matr₁)

    g : ∀ s → R s → pre C₂ Q s
    g = snd (snd Matr₂)

    h : ∀ s → P s → pre (C₁ :: C₂) Q s  --  ∀ s  → P s → pre C₁ (pre C₂ Q) s
    h s p = pre-mono {s = s} C₁ g (f s p)

vc-completeness (IF b THEN c₁ ELSE c₂) (H-If {P = P} {Q = Q} hyp₁ hyp₂) =
     (IF b THEN C₁ ELSE C₂) , A , D , h
     
  -- hyp₁ : |- [ (λ s → P s ∧ bval b s == true)  ] c₁ [ Q ]
  -- hyp₂ : |- [ (λ s → P s ∧ bval b s == false) ] c₂ [ Q ]

  where

    IH₁ : ∃[ C₁ ] ( c₁ == strip C₁ ∧ vc C₁ Q ∧ (∀ s → P s ∧ bval b s == true → pre C₁ Q s) )
    IH₁ = vc-completeness c₁ hyp₁

    IH₂ : ∃[ C₂ ] ( c₂ == strip C₂ ∧ vc C₂ Q ∧ (∀ s → P s ∧ bval b s == false → pre C₂ Q s) )
    IH₂ = vc-completeness c₂ hyp₂

    C₁ : Acom
    C₁ = fst IH₁

    C₂ : Acom
    C₂ = fst IH₂

    Matr₁ : c₁ == strip C₁ ∧ vc C₁ Q ∧ (∀ s → P s ∧ bval b s == true → pre C₁ Q s)
    Matr₁ = snd IH₁

    Matr₂ : c₂ == strip C₂ ∧ vc C₂ Q ∧ (∀ s → P s ∧ bval b s == false → pre C₂ Q s)
    Matr₂ = snd IH₂

    A : (IF b THEN c₁ ELSE c₂) == (IF b THEN strip C₁ ELSE strip C₂)
    A = begin
          IF b THEN c₁ ELSE c₂       ==⟨ cong (λ z → IF b THEN z ELSE c₂) (fst Matr₁) ⟩
          IF b THEN strip C₁ ELSE c₂ ==⟨ cong (λ z → IF b THEN strip C₁ ELSE z) (fst Matr₂)⟩
          IF b THEN strip C₁ ELSE strip C₂
        end

    D : vc C₁ Q ∧ vc C₂ Q
    D = (fst (snd Matr₁)) , (fst (snd Matr₂))

    f : ∀ s → P s ∧ bval b s == true → pre C₁ Q s
    f = snd (snd Matr₁)

    g : ∀ s → P s ∧ bval b s == false → pre C₂ Q s
    g = snd (snd Matr₂)

    if-pre : ∀{Q C₁ C₂} b s
         → (bval b s == true  → pre C₁ Q s)
         → (bval b s == false → pre C₂ Q s)
         →  pre (IF b THEN C₁ ELSE C₂) Q s
    if-pre b s f g with bval b s
    ... | true  = f refl
    ... | false = g refl

    h : ∀ s → P s → pre (IF b THEN C₁ ELSE C₂) Q s
    h s p = if-pre b s
                (λ x → f s (p , x))
                (λ y → g s (p , y))

vc-completeness (WHILE b DO c) (H-While {P} hyp) =
                (WHILE[ P ] b DO C) , (A , (D , (E , F)) , G)

  -- hyp : |- [ (λ s → P s ∧ bval b s == true) ] c [ P ]

  where

    IH : ∃[ C ] (c == strip C ∧ vc C P ∧ (∀ s → P s ∧ bval b s == true → pre C P s))
    IH = vc-completeness c hyp

    C : Acom
    C = fst IH

    Matr : c == strip C ∧ vc C P ∧ (∀ s → P s ∧ bval b s == true → pre C P s)
    Matr = snd IH

    A : (WHILE b DO c) == (WHILE b DO strip C)
    A = begin
          WHILE b DO c ==⟨ cong (λ z → WHILE b DO z) (fst Matr) ⟩ -- by ind. hyp.
          WHILE b DO strip C
        end

    D : ∀ s → P s ∧ bval b s == true → pre C P s
    D = snd (snd Matr)  -- by ind. hyp.

    E : ∀ s → P s ∧ bval b s == false → P s ∧ bval b s == false
    E s h = h

    F : vc C P
    F = fst (snd Matr)  -- by ind. hyp.

    G : ∀ s → P s → P s
    G s p = p


vc-completeness {P} {Q} c (H-Conseq {P'} {Q'} hyp₁ hyp hyp₂) = C , A , (D , E)

  -- hyp₁ : ∀ s → P s → P' s
  -- hyp  : |- [ P' ] c [ Q' ]
  -- hyp₂ : ∀ s → Q' s → Q s

  where
    IH : ∃[ C ] (c == strip C ∧ vc C Q' ∧ (∀ s → P' s → pre C Q' s) )
    IH = vc-completeness c hyp
  
    C : Acom
    C = fst IH

    Matr : c == strip C ∧ vc C Q' ∧ (∀ s → P' s → pre C Q' s)
    Matr = snd IH

    A : c == strip C
    A = fst Matr

    D : vc C Q
    D = vc-mono C hyp₂ (fst (snd Matr))

    f : ∀ s → P' s → pre C Q' s
    f = snd (snd Matr)

    E : ∀ s → P s → pre C Q s
    E s p = pre-mono C hyp₂ (f s (hyp₁ s p)) 

```
 
