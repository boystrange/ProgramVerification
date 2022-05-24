---
---

```agda
module Fun where

id : ∀{A : Set} -> A -> A
id = λ x -> x

const : ∀{A B : Set} -> A -> B -> A
const x = λ _ -> x

_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)
```
