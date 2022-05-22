---
layout: default
---

```agda
module Equality where

  open import Type

  data _==_ {A : Type} : A -> A -> Type where
    refl : ∀{x : A} -> x == x
  infix 4 _==_

  {-# BUILTIN EQUALITY _==_ #-}

  ==-symmetric : ∀{A : Type} {x y : A} -> x == y -> y == x
  ==-symmetric refl = refl

  ==-transitive : ∀{A : Type} {x y z : A} -> x == y -> y == z -> x == z
  ==-transitive refl refl = refl

  context : ∀{A B : Type} (f : A -> B) {x y : A} -> x == y -> f x == f y
  context _ refl = refl

  subst : ∀{A : Type} (P : A -> Type) {x y : A} -> x == y -> P x -> P y
  subst _ refl p = p

  begin_ : ∀{A : Set} (x : A) -> x == x
  begin_ _ = refl

  infix 2 begin_

  _end : ∀{A : Set} {x y : A} -> x == y -> x == y
  _end eq = eq

  infix 1 _end

  by-equals : ∀{A : Set} {x y : A} -> x == y -> (z : A) -> y == z -> x == z
  by-equals p _ q = ==-transitive p q

  by-refl : ∀{A : Set} (x : A) -> x == x -> x == x
  by-refl _ refl = refl

  syntax by-equals eq z reason = eq ==⟨ reason ⟩ z
  infixl 1 by-equals

  syntax by-refl z eq = eq ==⟨⟩ z
  infixl 1 by-refl
```
