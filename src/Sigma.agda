module Sigma where

-- data Σ (A : Set) (P : A -> Set) : Set where
--   _,_ : (x : A) -> P x -> Σ A P

-- fst : {A : Set} {P : A -> Set} -> Σ A P -> A
-- fst (x , _) = x

-- snd : {A : Set} {P : A -> Set} (p : Σ A P) -> P (fst p)
-- snd (_ , y) = y

record Σ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst

open Σ public

Σ-syntax : (A : Set) (P : A -> Set) -> Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x -> P) = Σ[ x ∈ A ] P

infix  2 Σ-syntax
infixr 4 _,_
