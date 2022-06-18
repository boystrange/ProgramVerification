module Equality where

open import Logic

infix  4 _==_ _!=_

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

_!=_ : {A : Set} -> A -> A -> Set
x != y = ¬ (x == y)

{-# BUILTIN EQUALITY _==_ #-}

symm : ∀{A : Set} {x y : A} -> x == y -> y == x
symm refl = refl

trans : ∀{A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl

cong : ∀{A B : Set} (f : A -> B) {x y : A} -> x == y -> f x == f y
cong _ refl = refl

cong2 : {A B C : Set} (f : A -> B -> C) {x y : A} {u v : B} -> x == y -> u == v -> f x u == f y v
cong2 _ refl refl = refl

subst : ∀{A : Set} (P : A -> Set) {x y : A} -> x == y -> P x -> P y
subst _ refl p = p
