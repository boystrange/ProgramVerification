module Library.Logic.Laws where

open import Library.Logic

∨-elim : {A B C : Set} -> (A -> C) -> (B -> C) -> A ∨ B -> C
∨-elim f g (inl x) = f x
∨-elim f g (inr x) = g x

ex-falso : ∀{A : Set} -> ⊥ -> A
ex-falso ()

contradiction : ∀{A : Set} -> A -> ¬ A -> ⊥
contradiction x ¬x = ¬x x

contraposition : ∀{A B : Set} -> (A -> B) -> ¬ B -> ¬ A
contraposition f nb a = nb (f a)
