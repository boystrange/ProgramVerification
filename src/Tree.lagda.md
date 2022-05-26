---
---

```agda
open import Nat

data Tree (A : Set) : Set where
  leaf : Tree A
  node : A -> Tree A -> Tree A -> Tree A

depth : ∀{A : Set} -> Tree A -> ℕ
depth leaf = 0
depth (node _ l r) = succ (max (depth l) (depth r))

leaves : ∀{A : Set} -> Tree A -> ℕ
leaves leaf = 1
leaves (node _ l r) = leaves l + leaves r

nodes : ∀{A : Set} -> Tree A -> ℕ
nodes leaf = 0
nodes (node _ l r) = succ (nodes l + nodes r)
```
