---
---

```agda
module Equality where

  open import Type

  data _==_ {A : Type} : A -> A -> Type where
    refl : ∀{x : A} -> x == x
  infix 4 _==_

  {-# BUILTIN EQUALITY _==_ #-}

  symm : ∀{A : Type} {x y : A} -> x == y -> y == x
  symm refl = refl

  trans : ∀{A : Type} {x y z : A} -> x == y -> y == z -> x == z
  trans refl refl = refl

  cong : ∀{A B : Type} (f : A -> B) {x y : A} -> x == y -> f x == f y
  cong _ refl = refl

  subst : ∀{A : Type} (P : A -> Type) {x y : A} -> x == y -> P x -> P y
  subst _ refl p = p

  begin_ : ∀{A : Set} {x y : A} -> x == y -> x == y
  begin_ p = p

  _end : ∀{A : Set} (x : A) -> x == x
  _end _ = refl

  _==⟨_⟩_ : ∀{A : Set} (x : A) {y z : A} -> x == y -> y == z -> x == z
  _==⟨_⟩_ _ = trans

  _==⟨⟩_ : ∀{A : Set} (x : A) {y : A} -> x == y -> x == y
  _ ==⟨⟩ p = p

  infix  1 begin_
  infixr 2 _==⟨⟩_ _==⟨_⟩_
  infix  3 _end
```
