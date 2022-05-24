---
title: Logic
---

```agda
open import Unit
open import Empty
open import Product
open import Sum

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

⊥-elim : ∀{A : Set} -> ⊥ -> A
⊥-elim ()

-- TODO: infix
```
