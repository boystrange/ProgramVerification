---
---

```agda
module RedBlackTree (A : Set) where

  open import Nat
  open import Nat.Properties
  open import Logic
  open import Product
  open import LessThan
  open import Equality

  data Order : Set where
    LT EQ GT : Order

  postulate compare : A -> A -> Order

  data RedBlackTree : ℕ -> Set
  data BlackTree : ℕ -> Set
  data RedTree : ℕ -> Set
  data RedRedTree : ℕ -> Set

  data RedBlackTree where
    red : ∀{n} -> RedTree n -> RedBlackTree n
    black : ∀{n} -> BlackTree n -> RedBlackTree n

  data BlackTree where
    leaf : BlackTree 1
    node : ∀{n} -> A -> RedBlackTree n -> RedBlackTree n -> BlackTree (succ n)

  data RedTree where
    node : ∀{n} -> A -> BlackTree n -> BlackTree n -> RedTree n

  data RedRedTree where
    red : ∀{n} -> RedTree n -> RedRedTree n
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

  depth : ∀{n} -> (ℕ -> ℕ -> ℕ) -> RedBlackTree n -> ℕ
  depth-red : ∀{n} -> (ℕ -> ℕ -> ℕ) -> RedTree n -> ℕ
  depth-black : ∀{n} -> (ℕ -> ℕ -> ℕ) -> BlackTree n -> ℕ

  depth f (red t) = depth-red f t
  depth f (black t) = depth-black f t

  depth-red f (node _ l r) = succ (f (depth-black f l) (depth-black f r))

  depth-black _ leaf = 0
  depth-black f (node _ l r) = succ (f (depth f l) (depth f r))

  min-depth : ∀{n} (t : RedBlackTree n) -> n <= succ (depth min t)
  min-depth-red : ∀{n} (t : RedTree n) -> n <= depth-red min t
  min-depth-black : ∀{n} (t : BlackTree n) -> n <= succ (depth-black min t)

  min-depth (red t) = <=-succ (min-depth-red t)
  min-depth (black t) = min-depth-black t

  min-depth-red (node _ l r) = <=min (min-depth-black l) (min-depth-black r)

  min-depth-black leaf = succ zero
  min-depth-black (node _ l r) = succ (<=min (min-depth l) (min-depth r))

  max-depth : ∀{n} (t : RedBlackTree n) -> depth max t < n + n
  max-depth-red : ∀{n} (t : RedTree n) -> depth-red max t < n + n
  max-depth-black : ∀{n} (t : BlackTree n) -> succ (depth-black max t) < n + n

  max-depth (red t) = max-depth-red t
  max-depth (black t) = <implies<= (max-depth-black t)

  max-depth-red (node _ l r) = <=max (max-depth-black l) (max-depth-black r)

  max-depth-black leaf = succ (succ zero)
  max-depth-black {succ n} (node _ l r) rewrite symm (+-succ n n) =
    succ (succ (<=max (max-depth l) (max-depth r)))

  theorem : ∀{n} (t : RedBlackTree n) -> depth max t <= depth min t + depth min t
  theorem (red t) = <implies<= (<=trans (max-depth-red t) (<=-cong-+ (min-depth-red t) (min-depth-red t)))
  theorem (black t) with max-depth-black t | min-depth-black t
  ... | M+2<=2n | n<=m+1 with <=-cong-+ n<=m+1 n<=m+1
  ... | 2n<=2m+2 rewrite symm (+-succ (depth-black min t) (depth-black min t)) =
    <=-succ-succ (<=-succ-succ (<=trans M+2<=2n 2n<=2m+2))
```
