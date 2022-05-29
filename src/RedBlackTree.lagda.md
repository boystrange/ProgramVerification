---
title: Red black trees
---

A red black tree is a binary search tree in which nodes are colored
(either red or black) and the following conditions are enforced:

1. Every leaf is black.
2. Every red node only has red children.
3. Every path from the root to one of the leaves goes through the
   number of black nodes.

We call **black height** the number of inner black nodes in a given
path. The condition (3) requires every path to have the same black
height.

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
```

We represent a red black tree using three distinct data types, `RedTree`, `BlackTree` and `RedBlackTree`. As their names suggest, they are used to represent red black trees having a red root, a black root and an uncertain root respectively. In this way, we can enforce the property that the children of a red-rooted tree are necessarily black, whereas the children of a black-rooted tree can be either red or black. In addition, each of these data types has a natural number as index which represents its black height. In this way, we can enforce the fact that sibling subtrees must have the same black height.

Clearly, these data types are mutually dependent on each other. For this reason, we cannot simply define them one after the other in an Agda script. Rather, we separate their *declaration* from their *definition*, so that all of them have been declared by the time they are defined.

A data type declaration resembles a data type definition, except for the fact that the `where` keyword is omitted and no costructor is given:

```agda
data RedBlackTree : ℕ -> Set
data BlackTree : ℕ -> Set
data RedTree : ℕ -> Set
```

A `RedBlackTree` with black height `n` is either a red tree with black height `n` or a black tree with black height `n`.

```agda
data RedBlackTree where
  red   : {n : ℕ} -> RedTree n -> RedBlackTree n
  black : {n : ℕ} -> BlackTree n -> RedBlackTree n
```

A `BlackTree` is either a `leaf` (which has black height 0) or a `node`, whose black height is one plus that of its two children. The children of a black node are red black trees, so their roots can be either red or black (and need not be of the same color).

```agda
data BlackTree where
  leaf : BlackTree 0
  node : {n : ℕ} -> A -> RedBlackTree n -> RedBlackTree n -> BlackTree (succ n)
```

A `RedTree` with black height `n` is necessarily a `node` (recall that leaves are black by convention) and its children are necessarily black-rooted trees with black height `n`.

```agda
data RedTree where
  node : {n : ℕ} -> A -> BlackTree n -> BlackTree n -> RedTree n
```

As it turns out, when we insert an element into a red black tree there can be a moment in which the tree is temporarily ill formed, in the sense that it violates condition (2) above. To accommodate the intermediate form we also introduce another data type, called `SomeTree`, which is either a plain red black tree or a red-rooted node in which one (but not both) of its children is also red.

```agda
data SomeTree : ℕ -> Set where
  plain : {n : ℕ} -> RedBlackTree n -> SomeTree n
  red-l : {n : ℕ} -> A -> RedTree n -> BlackTree n -> SomeTree n
  red-r : {n : ℕ} -> A -> BlackTree n -> RedTree n -> SomeTree n
```

```agda
balance-l : {n : ℕ} -> A -> SomeTree n -> RedBlackTree n -> RedBlackTree (succ n)
balance-l z (plain l) r = black (node z l r)
balance-l z (red-l y (node x a b) c) d =
  red (node y (node x (black a) (black b)) (node z (black c) d))
balance-l z (red-r y a (node x b c)) d =
  red (node x (node y (black a) (black b)) (node z (black c) d))

balance-r : {n : ℕ} -> A -> RedBlackTree n -> SomeTree n -> RedBlackTree (succ n)
balance-r z a (plain b) = black (node z a b)
balance-r z a (red-l y (node x b c) d) =
  red (node x (node z a (black b)) (node y (black c) (black d)))
balance-r z a (red-r y b (node x c d)) =
  red (node y (node z a (black b)) (node x (black c) (black d)))

into-red-black : {n : ℕ} -> A -> RedBlackTree n -> SomeTree n
into-black     : {n : ℕ} -> A -> BlackTree n -> RedBlackTree n
into-red       : {n : ℕ} -> A -> RedTree n -> SomeTree n

into-black x leaf = red (node x leaf leaf)
into-black x (node y l r) with compare x y
... | LT = balance-l y (into-red-black x l) r
... | EQ = black (node y l r)
... | GT = balance-r y l (into-red-black x r)

into-red x (node y l r) with compare x y
into-red x (node y l r) | EQ = plain (red (node y l r))
into-red x (node y l r) | LT with into-black x l
... | red t = red-l y t r
... | black t = plain (black t)
into-red x (node y l r) | GT with into-black x r
... | red t = red-r y l t
... | black t = plain (black t)

into-red-black x (black t) = plain (into-black x t)
into-red-black x (red t) = into-red x t

blacken : {n : ℕ} -> SomeTree n -> ∃[ m ] RedBlackTree m
blacken (plain (red (node x l r))) = _ , black (node x (black l) (black r))
blacken (plain (black t))          = _ , black t
blacken (red-l x l r)              = _ , black (node x (red l) (black r))
blacken (red-r x l r)              = _ , black (node x (black l) (red r))

insert : {n : ℕ} -> A -> RedBlackTree n -> ∃[ m ] RedBlackTree m
insert x t = blacken (into-red-black x t)
```

```agda
size* : {n : ℕ} -> RedBlackTree n -> ℕ
sizeR : {n : ℕ} -> RedTree n -> ℕ
sizeB : {n : ℕ} -> BlackTree n -> ℕ

size* (red   t) = sizeR t
size* (black t) = sizeB t

sizeR (node _ l r) = succ (sizeB l + sizeB r)

sizeB leaf = 0
sizeB (node _ l r) = succ (size* l + size* r)

⌊size*⌋ : {n : ℕ} (t : RedBlackTree n) -> 2 ^ n <= succ (size* t)
⌊sizeR⌋ : {n : ℕ} (t : RedTree n)      -> 2 ^ n <= sizeR t
⌊sizeB⌋ : {n : ℕ} (t : BlackTree n)    -> 2 ^ n <= succ (sizeB t)

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
```

```agda
depth* : {n : ℕ} -> RedBlackTree n -> ℕ
depthR : {n : ℕ} -> RedTree n -> ℕ
depthB : {n : ℕ} -> BlackTree n -> ℕ

depth* (red t) = depthR t
depth* (black t) = depthB t

depthR (node _ l r) = succ (max (depthB l) (depthB r))

depthB leaf = 0
depthB (node _ l r) = succ (max (depth* l) (depth* r))

⌈depth*⌉ : {n : ℕ} (t : RedBlackTree n) -> depth* t <= succ (2 * n)
⌈depthR⌉ : {n : ℕ} (t : RedTree n) -> depthR t <= succ (2 * n)
⌈depthB⌉ : {n : ℕ} (t : BlackTree n) -> depthB t <= 2 * n

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
