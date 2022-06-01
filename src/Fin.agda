module Fin where

open import Bool using (Bool; true; false)
open import Nat using (ℕ; zero; succ)

data Fin : ℕ -> Set where
  zero : ∀{n : ℕ} -> Fin (succ n)
  succ : ∀{n : ℕ} -> Fin n -> Fin (succ n)

_=?_ : ∀{n : ℕ} -> Fin n -> Fin n -> Bool
zero =? zero = true
zero =? succ y = false
succ x =? zero = false
succ x =? succ y = x =? y
