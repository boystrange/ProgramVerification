---
---

```agda
open import Nat
open import Product

Mat : Set
Mat = ℕ × ℕ × ℕ × ℕ

I : Mat
I = 1 , 0 ,
    0 , 1

F : Mat
F = 1 , 1 ,
    1 , 0

_*ₘ_ : Mat -> Mat -> Mat
(u , v ,
 x , y) *ₘ
 (a , b ,
  c , d) = u * a + v * c , u * b + v * d ,
           x * a + y * c , x * b + y * d

_^ₘ_ : ∀{n : ℕ} -> Mat -> ℕ -> Mat
M ^ₘ zero   = I
M ^ₘ succ k = M *ₘ (M ^ₘ k)

```
