module Exam.Divides where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.Equality

_divides_ : ℕ -> ℕ -> Set
m divides n = ∃[ k ] m * k == n

thm1 : {x y z : ℕ} -> z divides x -> z divides y -> z divides (x + y)
thm1 {z = z} (k₁ , refl) (k₂ , refl) = k₁ + k₂ , *-dist-l z k₁ k₂

thm2 : {x y z : ℕ} -> z divides x -> z divides y -> z divides (x * y)
thm2 {z = z} (k₁ , refl) (k₂ , refl) = k₁ * (z * k₂) , *-assoc z k₁ (z * k₂)

thm3 : {x : ℕ} -> 0 divides (succ x) -> 1 == 2
thm3 {x} (k , ())
