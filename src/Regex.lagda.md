---
---

```agda
module Regex where

  open import Bool hiding (_?=_)
  open import Char
  open import List
  open import List.Properties
  open import Equality
  open import Logic
  open import Product
  open import Sum

  infixr 7 _⊕_
  infixr 8 _·_
  infix  9 _⋆

  infix 4 _?=_

  postulate _?=_ : (x y : Char) -> x != y ∨ x == y

  data Regex : Set where
    ∅    : Regex
    ε    : Regex
    char : Char -> Regex
    _·_  : Regex -> Regex -> Regex
    _⊕_  : Regex -> Regex -> Regex
    _⋆   : Regex -> Regex

  Word : Set
  Word = List Char

  data Append {A : Set} : List A -> List A -> List A -> Set where
    append-[] : {ys : List A} -> Append [] ys ys
    append-:: : {x : A} {xs ys zs : List A} -> Append xs ys zs -> Append (x :: xs) ys (x :: zs)

  data _∈_ : Word -> Regex -> Set where
    match-eps      : [] ∈ ε
    match-char     : ∀(c : Char) -> (c :: []) ∈ char c
    match-seq      : {u v w : Word} {e f : Regex} -> u ∈ e -> v ∈ f -> Append u v w -> w ∈ (e · f)
    match-plus-l   : {u : Word} {e f : Regex} -> u ∈ e -> u ∈ (e ⊕ f)
    match-plus-r   : {u : Word} {e f : Regex} -> u ∈ f -> u ∈ (e ⊕ f)
    match-star-eps : {e : Regex} -> [] ∈ (e ⋆)
    match-star     : {u : Word} {e : Regex} -> u ∈ (e · e ⋆) -> u ∈ (e ⋆)

  eps : Regex -> Regex
  eps ∅ = ∅
  eps ε = ε
  eps (char x) = ∅
  eps (e · f) = eps e · eps f
  eps (e ⊕ f) = eps e ⊕ eps f
  eps (_ ⋆) = ε

  data Decidable (A : Set) : Set where
    yes :   A -> Decidable A
    no  : ¬ A -> Decidable A

  eps-decidable : (e : Regex) -> Decidable ([] ∈ e)
  eps-decidable ∅ = no (λ ())
  eps-decidable ε = yes match-eps
  eps-decidable (char x) = no (λ ())
  eps-decidable (e · f) with eps-decidable e | eps-decidable f
  ... | yes p | yes q = yes (match-seq p q append-[])
  ... | yes _ | no  q = no λ { (match-seq _ r append-[]) → q r }
  ... | no  p | _     = no λ { (match-seq r _ append-[]) → p r }
  eps-decidable (e ⊕ f) with eps-decidable e | eps-decidable f
  ... | yes p | _ = yes (match-plus-l p)
  ... | no  _ | yes p = yes (match-plus-r p)
  ... | no  p | no  q = no λ { (match-plus-l r) → p r
                             ; (match-plus-r r) → q r }
  eps-decidable (e ⋆) = yes match-star-eps

  _δ_ : Regex -> Char -> Regex
  ∅ δ c = ∅
  ε δ c = ∅
  char y δ x with x ?= y
  ... | left _ = ∅
  ... | right refl = ε
  (e · f) δ c = (e δ c) · f ⊕ eps e · (f δ c)
  (e ⊕ f) δ c = (e δ c) ⊕ (f δ c)
  (e ⋆) δ c   = (e δ c) · (e ⋆)

  eps-[] : {u : Word}{e : Regex} -> u ∈ eps e -> u == []
  eps-[] {e = ε}     match-eps        = refl
  eps-[] {e = e · f} (match-seq p q app) with eps-[] p | eps-[] q
  eps-[] {_} {e · f} (match-seq p q append-[]) | refl | refl = refl
  eps-[] {e = e ⊕ f} (match-plus-l p) = eps-[] p
  eps-[] {e = e ⊕ f} (match-plus-r p) = eps-[] p
  eps-[] {e = e ⋆}   match-eps        = refl

  eps-sound : {e : Regex} -> [] ∈ eps e -> [] ∈ e
  eps-sound {e = ε} match-eps = match-eps
  eps-sound {e = e · f} (match-seq p q append-[]) =
    match-seq (eps-sound p) (eps-sound q) append-[]
  eps-sound {e = e ⊕ f} (match-plus-l p) = match-plus-l (eps-sound p)
  eps-sound {e = e ⊕ f} (match-plus-r p) = match-plus-r (eps-sound p)
  eps-sound {e = e ⋆} match-eps = match-star-eps

  eps-complete : {e : Regex} -> [] ∈ e -> [] ∈ eps e
  eps-complete match-eps = match-eps
  eps-complete (match-seq p q append-[]) =
    match-seq (eps-complete p) (eps-complete q) append-[]
  eps-complete (match-plus-l p) = match-plus-l (eps-complete p)
  eps-complete (match-plus-r p) = match-plus-r (eps-complete p)
  eps-complete match-star-eps = match-eps
  eps-complete (match-star p) = match-eps

  δ-sound : {x : Char} {xs : Word} {e : Regex} -> xs ∈ (e δ x) -> (x :: xs) ∈ e
  δ-sound {x} {e = char y} p with x ?= y
  δ-sound {x} {_} {char x} match-eps | right refl = match-char x
  δ-sound {e = e · f} (match-plus-l (match-seq p q app)) =
    match-seq (δ-sound p) q (append-:: app)
  δ-sound {e = e · f} (match-plus-r (match-seq p q app)) with eps-[] p
  ... | refl with app
  ... | append-[] = match-seq (eps-sound p) (δ-sound q) append-[]
  δ-sound {e = e ⊕ f} (match-plus-l p) = match-plus-l (δ-sound p)
  δ-sound {e = e ⊕ f} (match-plus-r p) = match-plus-r (δ-sound p)
  δ-sound {e = e ⋆} (match-seq p q app) =
    match-star (match-seq (δ-sound p) q (append-:: app))

  δ-complete : {x : Char} {xs : Word} {e : Regex} -> (x :: xs) ∈ e -> xs ∈ (e δ x)
  δ-complete (match-char x) with x ?= x
  ... | left x!=x = absurd (x!=x refl)
  ... | right refl = match-eps
  δ-complete (match-seq p q append-[]) =
    match-plus-r (match-seq (eps-complete p) (δ-complete q) append-[])
  δ-complete (match-seq p q (append-:: app)) =
    match-plus-l (match-seq (δ-complete p) q app)
  δ-complete (match-plus-l p) = match-plus-l (δ-complete p)
  δ-complete (match-plus-r p) = match-plus-r (δ-complete p)
  δ-complete (match-star p) with δ-complete p
  ... | match-plus-l q = q
  ... | match-plus-r (match-seq q r app) with eps-[] q
  δ-complete (match-star p) | match-plus-r (match-seq q r append-[]) | refl = r

  match : (xs : Word) (e : Regex) -> Decidable (xs ∈ e)
  match [] e = eps-decidable e
  match (x :: xs) e with match xs (e δ x)
  ... | yes p = yes (δ-sound p)
  ... | no  q = no λ r -> q (δ-complete r)
```

Prove that `Append` is sound and complete w.r.t. the `++` function.

```agda
  append-sound : {A : Set} {xs ys zs : List A} -> Append xs ys zs -> xs ++ ys == zs
  append-sound append-[] = refl
  append-sound (append-:: app) = cong (_ ::_) (append-sound app)

  append-complete : {A : Set} (xs ys : List A) -> Append xs ys (xs ++ ys)
  append-complete [] ys = append-[]
  append-complete (_ :: xs) ys = append-:: (append-complete xs ys)
```
