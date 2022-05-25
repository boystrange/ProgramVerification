---
---

```agda
data Bool : Set where
  true false : Bool

if_then_else_ : ∀{A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

_=?_ : Bool -> Bool -> Bool
true =? true = true
true =? false = false
false =? true = false
false =? false = true

```
