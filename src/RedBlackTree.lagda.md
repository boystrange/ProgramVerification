---
---

```agda
module RedBlackTree (A : Set) where

  open import Nat
  open import Nat.Properties
  open import Logic
  open import Product
  open import LessThan
  open import LessThan.Reasoning
  open import Equality

  data Order : Set where
    LT EQ GT : Order

  postulate compare : A -> A -> Order

  data RedBlackTree : ℕ -> Set
  data BlackTree : ℕ -> Set
  data RedTree : ℕ -> Set

  data RedBlackTree where
    red   : ∀{n} -> RedTree n -> RedBlackTree n
    black : ∀{n} -> BlackTree n -> RedBlackTree n

  data BlackTree where
    leaf : BlackTree 0
    node : ∀{n} -> A -> RedBlackTree n -> RedBlackTree n -> BlackTree (succ n)

  data RedTree where
    node : ∀{n} -> A -> BlackTree n -> BlackTree n -> RedTree n

  data RedRedTree : ℕ -> Set where
    red   : ∀{n} -> RedTree n -> RedRedTree n
    black : ∀{n} -> BlackTree n -> RedRedTree n
    red-l : ∀{n} -> A -> RedTree n -> RedBlackTree n -> RedRedTree n
    red-r : ∀{n} -> A -> RedBlackTree n -> RedTree n -> RedRedTree n

  balance-l : ∀{n} -> A -> RedRedTree n -> RedBlackTree n -> RedBlackTree (succ n)
  balance-l z (red t) r = black (node z (red t) r)
  balance-l z (black t) r = black (node z (black t) r)
  balance-l z (red-l y (node x a b) c) d = red (node y (node x (black a) (black b)) (node z c d))
  balance-l z (red-r y a (node x b c)) d = red (node x (node y a (black b)) (node z (black c) d))

  balance-r : ∀{n} -> A -> RedBlackTree n -> RedRedTree n -> RedBlackTree (succ n)
  balance-r z a (red t) = black (node z a (red t))
  balance-r z a (black t) = black (node z a (black t))
  balance-r z a (red-l y (node x b c) d) = red (node x (node z a (black b)) (node y (black c) d))
  balance-r z a (red-r y b (node x c d)) = red (node y (node z a b) (node x (black c) (black d)))

  into-red-black : ∀{n} -> A -> RedBlackTree n -> RedRedTree n
  into-black     : ∀{n} -> A -> BlackTree n -> RedBlackTree n
  into-red       : ∀{n} -> A -> RedTree n -> RedRedTree n

  into-black x leaf = red (node x leaf leaf)
  into-black x (node y l r) with compare x y
  ... | LT = balance-l y (into-red-black x l) r
  ... | EQ = black (node y l r)
  ... | GT = balance-r y l (into-red-black x r)

  into-red x (node y l r) with compare x y
  into-red x (node y l r) | EQ = red (node y l r)
  into-red x (node y l r) | LT with into-black x l
  ... | red t = red-l y t (black r)
  ... | black t = black t
  into-red x (node y l r) | GT with into-black x r
  ... | red t = red-r y (black l) t
  ... | black t = black t

  into-red-black x (black t) with into-black x t
  ... | red   t = red t
  ... | black t = black t
  into-red-black x (red t) = into-red x t

  blacken : ∀{n} -> RedRedTree n -> ∃[ m ] RedBlackTree m
  blacken (red (node x l r)) = _ , black (node x (black l) (black r))
  blacken (black t) = _ , black t
  blacken (red-l x l r) = _ , black (node x (red l) r)
  blacken (red-r x l r) = _ , black (node x l (red r))

  insert : ∀{n} -> A -> RedBlackTree n -> ∃[ m ] RedBlackTree m
  insert x t = blacken (into-red-black x t)

  module Size where
    size* : ∀{n} -> RedBlackTree n -> ℕ
    sizeR : ∀{n} -> RedTree n -> ℕ
    sizeB : ∀{n} -> BlackTree n -> ℕ

    size* (red   t) = sizeR t
    size* (black t) = sizeB t

    sizeR (node _ l r) = succ (sizeB l + sizeB r)

    sizeB leaf = 0
    sizeB (node _ l r) = succ (size* l + size* r)

    ⌊size*⌋ : ∀{n} (t : RedBlackTree n) -> 2 ^ n <= succ (size* t)
    ⌊sizeR⌋ : ∀{n} (t : RedTree n)      -> 2 ^ n <= sizeR t
    ⌊sizeB⌋ : ∀{n} (t : BlackTree n)    -> 2 ^ n <= succ (sizeB t)

    ⌊size*⌋ (red   t) = <=-succ (⌊sizeR⌋ t)
    ⌊size*⌋ (black t) = ⌊sizeB⌋ t

    ⌊sizeR⌋ {n} (node _ l r) =
      begin
        2 ^ n                    ==⟨ +-zero (2 ^ n) ⟩
        2 ^ n + 0                <=⟨ <=-cong-+ (<=refl (2 ^ n)) zero ⟩
        2 ^ n + sizeB r          <=⟨ <=-cong-+ (⌊sizeB⌋ l) (<=refl (sizeB r)) ⟩
        succ (sizeB l) + sizeB r
      end

    ⌊sizeB⌋ leaf = succ zero
    ⌊sizeB⌋ {succ n} (node _ l r) =
      begin
        2 ^ n + (2 ^ n + 0)             ==⟨ symm (cong (2 ^ n +_) (+-zero (2 ^ n))) ⟩
        2 ^ n + 2 ^ n                   <=⟨ <=-cong-+ (⌊size*⌋ l) (⌊size*⌋ r) ⟩
        succ (size* l) + succ (size* r) ==⟨ symm (+-succ (succ (size* l)) (size* r)) ⟩
        succ (succ (size* l + size* r))
      end

  module Depth where

    depth* : ∀{n} -> RedBlackTree n -> ℕ
    depthR : ∀{n} -> RedTree n -> ℕ
    depthB : ∀{n} -> BlackTree n -> ℕ

    depth* (red t) = depthR t
    depth* (black t) = depthB t

    depthR (node _ l r) = succ (max (depthB l) (depthB r))

    depthB leaf = 0
    depthB (node _ l r) = succ (max (depth* l) (depth* r))

    ⌈depth*⌉ : ∀{n} (t : RedBlackTree n) -> depth* t <= succ (2 * n)
    ⌈depthR⌉ : ∀{n} (t : RedTree n) -> depthR t <= succ (2 * n)
    ⌈depthB⌉ : ∀{n} (t : BlackTree n) -> depthB t <= 2 * n

    ⌈depth*⌉ (red t) = ⌈depthR⌉ t
    ⌈depth*⌉ (black t) = <=-succ (⌈depthB⌉ t)

    ⌈depthR⌉ {n} (node _ l r) =
      succ (<=max (⌈depthB⌉ l) (⌈depthB⌉ r))

    ⌈depthB⌉ leaf = zero
    ⌈depthB⌉ {succ n} (node _ l r) =
      begin
        succ (max (depth* l) (depth* r)) <=⟨ succ (<=max (⌈depth*⌉ l) (⌈depth*⌉ r)) ⟩
        succ (succ (2 * n))              ==⟨ refl ⟩
        succ (succ (n + (n + 0)))        ==⟨ cong succ (+-succ n (n + 0)) ⟩
        succ (n + succ (n + 0))
      end
```
