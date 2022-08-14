module Logic.Laws where

open import Logic

ex-falso : ∀ {A : Set} → ⊥ → A
ex-falso = λ ()

contrad : ∀ {A : Set} → A → ¬ A → ⊥
contrad x ¬x = ¬x x
