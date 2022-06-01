module Logic where

open import Unit
open import Empty
open import Product
open import Sum

-- TODO: infix

infixr 2 _∨_ ∃-syntax
infixr 3 _∧_

⊤ : Set
⊤ = Unit

⊥ : Set
⊥ = Empty

_∧_ : Set -> Set -> Set
_∧_ = _×_

_∨_ : Set -> Set -> Set
_∨_ = _⊎_

¬ : Set -> Set
¬ A = A -> ⊥

data Decidable (A : Set) : Set where
  yes :   A -> Decidable A
  no  : ¬ A -> Decidable A

absurd : ∀{A : Set} -> ⊥ -> A
absurd ()

∃ : ∀{A : Set} -> (A -> Set) -> Set
∃ = Σ _

∃-syntax : ∀{A : Set} -> (A -> Set) -> Set
∃-syntax = ∃

syntax ∃-syntax (λ x -> B) = ∃[ x ] B
