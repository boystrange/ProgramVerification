---
title: Sum
---

```agda
data _⊎_ (A B : Set) : Set where
  left  : A -> A ⊎ B
  right : B -> A ⊎ B

⊎-elim : ∀{A B C : Set} -> A ⊎ B -> (A -> C) -> (B -> C) -> C
⊎-elim (left x)  f _ = f x
⊎-elim (right x) _ g = g x
```
