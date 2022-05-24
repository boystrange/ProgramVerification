---
title: Product
---

```agda
module Product where

open import Sigma public

_×_ : Set -> Set -> Set
A × B = Σ A λ _ -> B

infixr 2 _×_
```
