---
title: Red black trees
---

A red black tree is a binary search tree in which nodes are colored
(either red or black) and the following conditions are enforced:

1. Every red node only has red children.
2. Every path from the root to one of the leaves goes through the
   number of black nodes.

The combination of these properties makes sure that the depth of a red black tree cannot be more than twice the length of the shortest path from its root to one of its leaves. So, a red black tree is reasonably balanced.

```agda
module Chapter.Fun.RedBlackTree (A : Set) (_≼_ : A -> A -> Set) where

open import Library.Nat
open import Library.Nat.Properties
open import Library.Logic
open import Library.LessThan
open import Library.LessThan.Reasoning
open import Library.Equality

data Order : Set where
  LT EQ GT : Order

postulate compare : A -> A -> Order
```

We represent a red black tree using three distinct data types,
`RedTree`, `BlackTree` and `RedBlackTree`. As suggested by their
names, the root of a `RedTree` is certainly red, the root of a
`BlackTree` is certainly black, whereas the root of a `RedBlackTree`
can be either red or black. By devising distinct data types, we can
enforce the property (1) of red black trees requiring that the
children of a red-rooted tree must be black, as opposed to the
children of a black-rooted tree that can be either red or black. In
addition, we index these data types with a natural number called
**black height**. Intuitively, the black height of a tree is the
number of inner black nodes along the paths from the root to its
leaves. By making sure that the children of a tree have the same
black height, we enforce the property (2) of red black trees.

Clearly, these data types are mutually dependent on each other. For
this reason, we cannot simply define them one after the other in an
Agda script. Rather, we must separate their *declaration* from their
*definition* so that all of them have been declared by the time they
are defined.

A data type declaration starts like a data type definition, but the
`where` keyword is omitted and no costructor is given:

```agda
data RedTree : ℕ -> Set
data BlackTree : ℕ -> Set
data RedBlackTree : ℕ -> Set
```

These statements make Agda aware of the fact that from now on we may
refer to these data types, even though we haven't defined their
constructors yet. To do so, we now provide further `data`
definitions, this time omitting the type signature of the data type
being defined but listing their constructors. In particular, a
`RedTree` with black height `n` is necessarily an inner `node`
(leaves are black by convention) and its children are necessarily
black-rooted trees with black height `n`.

```agda
data RedTree where
  node : {n : ℕ} -> A -> BlackTree n -> BlackTree n -> RedTree n
```

A `BlackTree` is either a `leaf` (which has black height 0) or an
inner `node`, whose black height is one plus that of its two
children. The children of a black node are red black trees, so their
roots can be either red or black (and need not be of the same
color).

```agda
data BlackTree where
  leaf : BlackTree 0
  node : {n : ℕ} -> A -> RedBlackTree n -> RedBlackTree n -> BlackTree (succ n)
```

Finally, a `RedBlackTree` with black height `n` is either a red tree
or a black tree with the same black height.

```agda
data RedBlackTree where
  red   : {n : ℕ} -> RedTree n -> RedBlackTree n
  black : {n : ℕ} -> BlackTree n -> RedBlackTree n
```

When we insert an element into a red black tree there can be a
moment in which the tree is temporarily unbalanced, in the sense
that it violates condition (1) above. To accommodate the
intermediate form we also introduce yet another data type, called
`SomeTree`, which is either a plain red black tree or a red-rooted
tree in which one of its children is black but the other is red Note
that we distinguish between a "left" unbalanced tree (constructor
`red-l`) from a "right" unbalanced tree (constructor `red-r`).

```agda
data SomeTree : ℕ -> Set where
  plain : {n : ℕ} -> RedBlackTree n -> SomeTree n
  red-l : {n : ℕ} -> A -> RedTree n -> BlackTree n -> SomeTree n
  red-r : {n : ℕ} -> A -> BlackTree n -> RedTree n -> SomeTree n
```

The next two functions implement a *balancing* operation. In
particular, `balance-l x l r` balances a hypothetical black-rooted
tree having `x` in its root, a possibly unbalanced left child `l`
and a balanced right child `r`. The function `balance-r x l r` does
the same for a tree in which the right child is possibly
unbalanced. The balancing operation is achieved by performing a
suitable rotation of the tree structure while preserving the
ordering between the elements in the tree. The re-balanced tree
turns out to have the same black height of the (hypothetical)
unbalanced one.

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
```

```agda
insertR : {n : ℕ} -> A -> RedTree n -> SomeTree n
insertB : {n : ℕ} -> A -> BlackTree n -> RedBlackTree n
insert* : {n : ℕ} -> A -> RedBlackTree n -> SomeTree n
```

```agda
insertR x (node y l r) with compare x y
insertR x (node y l r) | EQ = plain (red (node y l r))
insertR x (node y l r) | LT with insertB x l
... | red t = red-l y t r
... | black t = plain (black t)
insertR x (node y l r) | GT with insertB x r
... | red t = red-r y l t
... | black t = plain (black t)

insertB x leaf = red (node x leaf leaf)
insertB x (node y l r) with compare x y
... | LT = balance-l y (insert* x l) r
... | EQ = black (node y l r)
... | GT = balance-r y l (insert* x r)

insert* x (black t) = plain (insertB x t)
insert* x (red t) = insertR x t

blacken : {n : ℕ} -> SomeTree n -> ∃[ m ] RedBlackTree m
blacken (plain (red (node x l r))) = _ , black (node x (black l) (black r))
blacken (plain (black t))          = _ , black t
blacken (red-l x l r)              = _ , black (node x (red l) (black r))
blacken (red-r x l r)              = _ , black (node x (black l) (red r))

insert : {n : ℕ} -> A -> RedBlackTree n -> ∃[ m ] RedBlackTree m
insert x t = blacken (insert* x t)
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

⌊size*⌋ (red   t) = le-succ-r (⌊sizeR⌋ t)
⌊size*⌋ (black t) = ⌊sizeB⌋ t

⌊sizeR⌋ {n} (node _ l r) =
  begin
    2 ^ n                    ==⟨ symm (+-unit-r (2 ^ n)) ⟩
    2 ^ n + 0                <=⟨ le-cong-+ le-refl le-zero ⟩
    2 ^ n + sizeB r          <=⟨ le-cong-+ (⌊sizeB⌋ l) le-refl ⟩
    succ (sizeB l) + sizeB r
  end

⌊sizeB⌋ leaf = le-succ le-zero
⌊sizeB⌋ {succ n} (node _ l r) =
  begin
    2 ^ n + (2 ^ n + 0)             ==⟨ symm (cong (2 ^ n +_) (symm (+-unit-r (2 ^ n)))) ⟩
    2 ^ n + 2 ^ n                   <=⟨ le-cong-+ (⌊size*⌋ l) (⌊size*⌋ r) ⟩
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
⌈depth*⌉ (black t) = le-succ-r (⌈depthB⌉ t)

⌈depthR⌉ {n} (node _ l r) =
  le-succ (le-max (⌈depthB⌉ l) (⌈depthB⌉ r))

⌈depthB⌉ leaf = le-zero
⌈depthB⌉ {succ n} (node _ l r) =
  begin
    succ (max (depth* l) (depth* r)) <=⟨ le-succ (le-max (⌈depth*⌉ l) (⌈depth*⌉ r)) ⟩
    succ (succ (2 * n))              ==⟨ refl ⟩
    succ (succ (n + (n + 0)))        ==⟨ cong succ (+-succ n (n + 0)) ⟩
    succ (n + succ (n + 0))
  end
```
