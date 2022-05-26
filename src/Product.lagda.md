---
title: Product
---

```agda
module Product where

open import Sigma public

infixr 2 _×_

_×_ : Set -> Set -> Set
A × B = Σ A λ _ -> B
```
