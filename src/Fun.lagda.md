---
---

```agda
module Fun where

open import Product

id : ∀{A : Set} -> A -> A
id = λ x -> x

const : ∀{A B : Set} -> A -> B -> A
const x = λ _ -> x

_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)

curry : ∀{A B C : Set} -> (A × B -> C) -> A -> B -> C
curry f x y = f (x , y)

uncurry : ∀{A B C : Set} -> (A -> B -> C) -> A × B -> C
uncurry f (x , y) = f x y

flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x
```
