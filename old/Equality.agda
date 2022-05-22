
open import Type

infix 2 _==_

data _==_ {A : Type} : A -> A -> Type where
  refl : {x : A} -> x == x

{-# BUILTIN EQUALITY _==_ #-}

==-reflexive : ∀{A : Type} {x : A} -> x == x
==-reflexive = refl

==-symmetric : ∀{A : Type} {x y : A} -> x == y -> y == x
==-symmetric refl = refl

==-transitive : ∀{A : Type} {x y z : A} -> x == y -> y == z -> x == z
==-transitive refl refl = refl

context : ∀{A B : Type} -> (f : A -> B) -> ∀{x y : A} -> x == y -> f x == f y
context f refl = refl
