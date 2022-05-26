---
---

```agda
module Equality where

infix  1 begin_
infixr 2 _==⟨⟩_ _==⟨_⟩_
infix  3 _end
infix  4 _==_

data _==_ {A : Set} : A -> A -> Set where
  refl : ∀{x : A} -> x == x

{-# BUILTIN EQUALITY _==_ #-}

symm : ∀{A : Set} {x y : A} -> x == y -> y == x
symm refl = refl

trans : ∀{A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

cong : ∀{A B : Set} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong _ refl = refl

subst : ∀{A : Set} (P : A -> Set) {x y : A} -> x == y -> P x -> P y
subst _ refl p = p

begin_ : ∀{A : Set} {x y : A} -> x == y -> x == y
begin_ p = p

_end : ∀{A : Set} (x : A) -> x == x
_end _ = refl

_==⟨_⟩_ : ∀{A : Set} (x : A) {y z : A} -> x == y -> y == z -> x == z
_==⟨_⟩_ _ = trans

_==⟨⟩_ : ∀{A : Set} (x : A) {y : A} -> x == y -> x == y
_ ==⟨⟩ p = p
```
