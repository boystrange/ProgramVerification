---
---

```agda
module Chapter.Fun.RegularExpressions where

open import Library.Nat using (ℕ)
open import Library.Nat.Properties using (_=?_)
open import Library.List
open import Library.Equality
open import Library.Logic
open import Library.Logic.Laws

infixr 7 _+_
infixr 8 _·_
infix  9 _*

Symbol : Set
Symbol = ℕ

Word : Set
Word = List Symbol

data Regex : Set where
  ∅   : Regex
  ε   : Regex
  sym : Symbol -> Regex
  _·_ : Regex -> Regex -> Regex
  _+_ : Regex -> Regex -> Regex
  _*  : Regex -> Regex

data Append {A : Set} : List A -> List A -> List A -> Set where
  append-[] : {ys : List A} -> Append [] ys ys
  append-:: : {x : A} {xs ys zs : List A} -> Append xs ys zs -> Append (x :: xs) ys (x :: zs)

data _∈_ : Word -> Regex -> Set where
  [eps]      : [] ∈ ε
  [sym]      : (c : Symbol) -> (c :: []) ∈ sym c
  [seq]      : {u v w : Word} {e f : Regex} -> u ∈ e -> v ∈ f -> Append u v w -> w ∈ (e · f)
  [plus-l]   : {u : Word} {e f : Regex} -> u ∈ e -> u ∈ (e + f)
  [plus-r]   : {u : Word} {e f : Regex} -> u ∈ f -> u ∈ (e + f)
  [star-eps] : {e : Regex} -> [] ∈ (e *)
  [star]     : {u : Word} {e : Regex} -> u ∈ (e · e *) -> u ∈ (e *)

eps : Regex -> Regex
eps ∅ = ∅
eps ε = ε
eps (sym x) = ∅
eps (e · f) = eps e · eps f
eps (e + f) = eps e + eps f
eps (_ *) = ε

δ : Regex -> Symbol -> Regex
δ ∅ c = ∅
δ ε c = ∅
δ (sym y) x with x =? y
... | inl _ = ∅
... | inr refl = ε
δ (e · f) c = δ e c · f + eps e · δ f c
δ (e + f) c = δ e c + δ f c
δ (e *) c   = δ e c · (e *)

eps-[] : {u : Word}{e : Regex} -> u ∈ eps e -> u == []
eps-[] {e = ε}     [eps]        = refl
eps-[] {e = e · f} ([seq] p q app) with eps-[] p | eps-[] q
eps-[] {e = e · f} ([seq] p q append-[]) | refl | refl = refl
eps-[] {e = e + f} ([plus-l] p) = eps-[] p
eps-[] {e = e + f} ([plus-r] p) = eps-[] p
eps-[] {e = e *}   [eps]        = refl

eps-sound : {e : Regex} -> [] ∈ eps e -> [] ∈ e
eps-sound {e = ε}     [eps] = [eps]
eps-sound {e = e · f} ([seq] p q append-[]) =
  [seq] (eps-sound p) (eps-sound q) append-[]
eps-sound {e = e + f} ([plus-l] p) = [plus-l] (eps-sound p)
eps-sound {e = e + f} ([plus-r] p) = [plus-r] (eps-sound p)
eps-sound {e = e *}   [eps] = [star-eps]

eps-complete : {e : Regex} -> [] ∈ e -> [] ∈ eps e
eps-complete [eps]        = [eps]
eps-complete ([seq] p q append-[]) =
  [seq] (eps-complete p) (eps-complete q) append-[]
eps-complete ([plus-l] p) = [plus-l] (eps-complete p)
eps-complete ([plus-r] p) = [plus-r] (eps-complete p)
eps-complete [star-eps]   = [eps]
eps-complete ([star] p)   = [eps]

δ-sound : {x : Symbol} {xs : Word} {e : Regex} -> xs ∈ δ e x -> (x :: xs) ∈ e
δ-sound {x} {e = sym y} p with x =? y
δ-sound {x} {_} {sym x} [eps] | inr refl = [sym] x
δ-sound {e = e · f} ([plus-l] ([seq] p q app)) =
  [seq] (δ-sound p) q (append-:: app)
δ-sound {e = e · f} ([plus-r] ([seq] p q app)) with eps-[] p
... | refl with app
... | append-[] = [seq] (eps-sound p) (δ-sound q) append-[]
δ-sound {e = e + f} ([plus-l] p) = [plus-l] (δ-sound p)
δ-sound {e = e + f} ([plus-r] p) = [plus-r] (δ-sound p)
δ-sound {e = e *} ([seq] p q app) =
  [star] ([seq] (δ-sound p) q (append-:: app))

δ-complete : {x : Symbol} {xs : Word} {e : Regex} -> (x :: xs) ∈ e -> xs ∈ δ e x
δ-complete ([sym] x) with x =? x
... | inl x!=x = ex-falso (x!=x refl)
... | inr refl = [eps]
δ-complete ([seq] p q append-[]) =
  [plus-r] ([seq] (eps-complete p) (δ-complete q) append-[])
δ-complete ([seq] p q (append-:: app)) =
  [plus-l] ([seq] (δ-complete p) q app)
δ-complete ([plus-l] p) = [plus-l] (δ-complete p)
δ-complete ([plus-r] p) = [plus-r] (δ-complete p)
δ-complete ([star] p) with δ-complete p
... | [plus-l] q = q
... | [plus-r] ([seq] q r app) with eps-[] q
δ-complete ([star] p) | [plus-r] ([seq] q r append-[]) | refl = r

eps-decidable : (e : Regex) -> Decidable ([] ∈ e)
eps-decidable ∅ = inl λ ()
eps-decidable ε = inr [eps]
eps-decidable (sym x) = inl λ ()
eps-decidable (e · f) with eps-decidable e | eps-decidable f
... | inr p | inr q = inr ([seq] p q append-[])
... | inr _ | inl q = inl λ { ([seq] _ r append-[]) → q r }
... | inl p | _     = inl λ { ([seq] r _ append-[]) → p r }
eps-decidable (e + f) with eps-decidable e | eps-decidable f
... | inr p | _ = inr ([plus-l] p)
... | inl _ | inr p = inr ([plus-r] p)
... | inl p | inl q = inl λ { ([plus-l] r) → p r
                            ; ([plus-r] r) → q r }
eps-decidable (e *) = inr [star-eps]

match : (xs : Word) (e : Regex) -> Decidable (xs ∈ e)
match [] e = eps-decidable e
match (x :: xs) e with match xs (δ e x)
... | inr p = inr (δ-sound p)
... | inl q = inl λ r -> q (δ-complete r)
```

Simple test

```agda
`a : Symbol
`a = 0

`b : Symbol
`b = 1

`c : Symbol
`c = 2

e : Regex
e = (sym `a · sym `b) *

s1 : Word
s1 = `a :: `b :: `a :: `b :: []

s2 : Word
s2 = `a :: `b :: `a :: []
```

Try evaluate `match s1 e` and `match s2 e` using `C-c C-n`

Prove that `Append` is sound and complete w.r.t. the `++` function.

```agda
append-sound : {A : Set} {xs ys zs : List A} -> Append xs ys zs -> xs ++ ys == zs
append-sound append-[] = refl
append-sound (append-:: app) = cong (_ ::_) (append-sound app)

append-complete : {A : Set} (xs ys : List A) -> Append xs ys (xs ++ ys)
append-complete [] ys = append-[]
append-complete (_ :: xs) ys = append-:: (append-complete xs ys)
```
