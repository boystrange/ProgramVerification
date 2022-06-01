module Sigma where

record Σ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ public

infixr 4 _,_
