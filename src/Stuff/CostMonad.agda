module CostMonad where
  open import Nat
  open import Nat.Properties
  open import Equality
  open import LessThan

  private
    module Dummy where
      infix 1 _in-time_
      data _in-time_ (A : Set) (n : ℕ) : Set where
        box : A -> A in-time n

    open Dummy using (_in-time_)
    open Dummy

    unbox : {A : Set} {n : ℕ} -> A in-time n -> A
    unbox (box x) = x

  infixl 1 _>>=_
  _>>=_ : {A B : Set} {n m : ℕ} -> A in-time n -> (A -> B in-time m) -> B in-time (n + m)
  box x >>= f = box (unbox (f x))

  -- _=<<_ : ∀ {a b} {A : Set a} {B : Set b} -> {n m : ℕ} -> (A -> B in-time m) -> A in-time n -> B in-time (n + m)
  -- _=<<_ = flip _>>=_

  infixr 2 _<$>_
  _<$>_ : {A B : Set} {n : ℕ} -> (A -> B) -> A in-time n -> B in-time n
  f <$> box x = box (f x)

  -- _<$$>_ : ∀ {a b} {A : Set a} {B : Set b} -> {n : ℕ} -> A in-time n -> (A -> B) -> B in-time n
  -- _<$$>_ = flip _<$>_

  return : {A : Set} {n : ℕ} -> A -> A in-time n
  return = box

  bound== : {A : Set} {m n : ℕ} -> (m == n) -> A in-time m -> A in-time n
  bound== refl p = p

  bound+ : {A : Set} {m n k : ℕ} -> (m + k == n) -> A in-time m -> A in-time n
  bound+ eq x = bound== eq (x >>= return)

  bound<= : {A : Set} {m n : ℕ} -> (m <= n) -> A in-time m -> A in-time n
  bound<= le = bound+ (lem le)
    where
    lem : ∀ {m n} -> (m <= n) -> m + (n - m) == n
    lem zero = -zero _
    lem (succ p) = cong succ (lem p)
