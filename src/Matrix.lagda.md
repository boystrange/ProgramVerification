---
---

```agda
open import Fun
open import Bool
open import Nat
open import Fin
-- open import Vec
open import Product
open import Equality

Vector : ℕ -> Set
Vector n = Fin n -> ℕ

Matrix : ℕ -> ℕ -> Set
Matrix m n = Fin m -> Fin n -> ℕ

1ₘ : ∀{n : ℕ} -> Matrix n n
1ₘ zero     zero     = 1
1ₘ zero     (succ _) = 0
1ₘ (succ _) zero     = 0
1ₘ (succ i) (succ j) = 1ₘ i j

transpose : ∀{m n : ℕ} -> Matrix m n -> Matrix n m
transpose M i j = M j i

postulate
  extensionality : ∀{A B : Set} {f g : A -> B} -> (∀(x : A) -> f x == g x) -> f == g

extensionality² : ∀{A B C : Set} {f g : A -> B -> C} -> (∀(x : A) (y : B) -> f x y == g x y) -> f == g
extensionality² {f = f} {g = g} h = extensionality λ x -> extensionality λ y -> h x y

transpose-involution : ∀{m n : ℕ} (M : Matrix m n) -> transpose (transpose M) == M
transpose-involution M = extensionality² λ j i -> refl

row : ∀{m n : ℕ} (i : Fin m) -> Matrix m n -> Vector n
row i M = M i

column : ∀{m n : ℕ} (j : Fin n) -> Matrix m n -> Vector m
column j M i = M i j

tail : ∀{n : ℕ} -> Vector (succ n) -> Vector n
tail V i = V (succ i)

sum : ∀{n : ℕ} -> Vector n -> ℕ
sum {zero} V = 0
sum {succ n} V = V zero + sum (tail V)

zip-with : ∀{n : ℕ} -> (ℕ -> ℕ -> ℕ) -> Vector n -> Vector n -> Vector n
zip-with f V W i = f (V i) (W i)

_·_ : ∀{n : ℕ} -> Vector n -> Vector n -> ℕ
V · W = sum (zip-with _*_ V W)

_+ₘ_ : ∀{m n : ℕ} -> Matrix m n -> Matrix m n -> Matrix m n
(M +ₘ N) i j = M i j + N i j

_*ₘ_ : ∀{m n k : ℕ} -> Matrix m k -> Matrix k n -> Matrix m n
(M *ₘ N) i j = row i M · column j N

_^ₘ_ : ∀{n : ℕ} -> Matrix n n -> ℕ -> Matrix n n
M ^ₘ zero   = 1ₘ
M ^ₘ succ k = M *ₘ (M ^ₘ k)

Iₘ : Matrix 2 2
Iₘ zero        zero        = 1
Iₘ zero        (succ zero) = 1
Iₘ (succ zero) zero        = 1
Iₘ (succ zero) (succ zero) = 0

fibo : ℕ -> ℕ
fibo 0 = 0
fibo 1 = 1
fibo (succ (succ n)) = fibo n + fibo (succ n)

Fₘ : ℕ -> Matrix 2 2
Fₘ k zero zero = fibo (succ k)
Fₘ k zero (succ zero) = fibo k
Fₘ k (succ zero) zero = fibo k
Fₘ k (succ zero) (succ zero) = fibo (succ k)

lemma00 : ∀(k : ℕ) -> (Iₘ *ₘ Fₘ k) zero zero == fibo (succ (succ k))
lemma00 k = {!!}

lemma1 : ∀(k : ℕ) -> Iₘ *ₘ Fₘ k == Fₘ (succ k)
lemma1 k = extensionality² λ { zero zero → {!!}
                             ; zero (succ zero) → {!!}
                             ; (succ zero) zero → {!!}
                             ; (succ zero) (succ zero) → {!!} }

lemma : ∀(k : ℕ) -> Iₘ ^ₘ k == Fₘ k
lemma zero = extensionality² λ { zero zero → refl
                               ; zero (succ zero) → refl
                               ; (succ zero) zero → refl
                               ; (succ zero) (succ zero) → refl }
lemma (succ k) rewrite lemma k = lemma1 k
```

