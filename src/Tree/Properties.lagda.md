---
---

```agda
module Tree.Properties where

open import Nat
open import Tree
open import Nat.Properties
open import Equality

leaves-nodes : ∀{A : Set} (t : Tree A) -> leaves t == succ (nodes t)
leaves-nodes leaf = refl
leaves-nodes (node x l r) =
  begin
    leaves (node x l r)             ==⟨⟩
    leaves l + leaves r             ==⟨ cong (_+ leaves r) (leaves-nodes l) ⟩
    succ (nodes l) + leaves r       ==⟨ cong (succ (nodes l) +_) (leaves-nodes r) ⟩
    succ (nodes l) + succ (nodes r) ==⟨⟩
    succ (nodes l + succ (nodes r)) ==⟨ cong succ (symm (+-succ (nodes l) (nodes r))) ⟩
    succ (succ (nodes l + nodes r)) ==⟨⟩
    succ (nodes (node x l r))
  end

```
