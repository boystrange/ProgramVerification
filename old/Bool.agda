
open import Type
open import Equality

data 𝔹 : Type where
  true : 𝔹
  false : 𝔹

not : 𝔹 -> 𝔹
not true  = false
not false = true

_&&_ : 𝔹 -> 𝔹 -> 𝔹
true  && b = b
false && _ = false

_||_ : 𝔹 -> 𝔹 -> 𝔹
true  || _ = true
false || b = b

infixl 3 _&&_ _||_

double-negation : ∀(b : 𝔹) -> b == not (not b)
double-negation true = refl
double-negation false = refl

&&-associative : ∀(x y z : 𝔹) -> x && (y && z) == (x && y) && z
&&-associative true y z = refl
&&-associative false y z = refl

de-morgan-1 : ∀(x y : 𝔹) -> not (x && y) == not x || not y
de-morgan-1 true y = refl
de-morgan-1 false y = refl

if_then_else_ : ∀{A : Type} -> 𝔹 -> A -> A -> A
if true then x else y = x
if false then x else y = y
