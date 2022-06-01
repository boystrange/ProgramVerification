module Fin where

open import Nat using (ℕ; zero; succ)
open import Logic
open import Equality

data Fin : ℕ -> Set where
  zero : ∀{n : ℕ} -> Fin (succ n)
  succ : ∀{n : ℕ} -> Fin n -> Fin (succ n)

_=?_ : ∀{n : ℕ} (i j : Fin n) -> Decidable (i == j)
zero =? zero = yes refl
zero =? succ j = no λ ()
succ i =? zero = no (λ ())
succ i =? succ j with i =? j
... | yes refl = yes refl
... | no neq = no  λ { refl -> neq refl }
