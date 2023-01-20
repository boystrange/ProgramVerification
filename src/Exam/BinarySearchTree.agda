module Exam.BinarySearchTree where

open import Library.Nat
open import Library.LessThan
open import Exam.Trichotomy

data Tree (A : Set) : Set where
  leaf : Tree A
  node : A -> Tree A -> Tree A -> Tree A

data UpperBound (n : ℕ) : Tree ℕ -> Set where
  ub-leaf : UpperBound n leaf
  ub-node : {m : ℕ} {t s : Tree ℕ} -> m < n -> UpperBound n t ->
            UpperBound n s -> UpperBound n (node m t s)

data LowerBound (n : ℕ) : Tree ℕ -> Set where
  lb-leaf : LowerBound n leaf
  lb-node : {m : ℕ} {t s : Tree ℕ} -> n < m -> LowerBound n t ->
            LowerBound n s -> LowerBound n (node m t s)

data BST : Tree ℕ -> Set where
  bst-leaf : BST leaf
  bst-node : {n : ℕ} {t s : Tree ℕ} -> UpperBound n t ->
             LowerBound n s -> BST t -> BST s -> BST (node n t s)

insert : ℕ -> Tree ℕ -> Tree ℕ
insert x leaf = node x leaf leaf
insert x (node y t s) with trichotomy x y
... | LT p = node y (insert x t) s
... | EQ p = node y t s
... | GT p = node y t (insert x s)

insert-upper-bound : (x : ℕ) {y : ℕ} {t : Tree ℕ} -> x < y ->
                     UpperBound y t -> UpperBound y (insert x t)
insert-upper-bound x lt ub-leaf = ub-node lt ub-leaf ub-leaf
insert-upper-bound x lt (ub-node {z} z<y t s) with trichotomy x z
... | LT p = ub-node z<y (insert-upper-bound x lt t) s
... | EQ p = ub-node z<y t s
... | GT p = ub-node z<y t (insert-upper-bound x lt s)

insert-lower-bound : (x : ℕ) {y : ℕ} {t : Tree ℕ} -> y < x ->
                     LowerBound y t -> LowerBound y (insert x t)
insert-lower-bound x lt lb-leaf = lb-node lt lb-leaf lb-leaf
insert-lower-bound x lt (lb-node {z} y<z t s) with trichotomy x z
... | LT p = lb-node y<z (insert-lower-bound x lt t) s
... | EQ p = lb-node y<z t s
... | GT p = lb-node y<z t (insert-lower-bound x lt s)

insert-bst : (x : ℕ) {t : Tree ℕ} -> BST t -> BST (insert x t)
insert-bst x bst-leaf = bst-node ub-leaf lb-leaf bst-leaf bst-leaf
insert-bst x (bst-node {y} ub lb t s) with trichotomy x y
... | LT p = bst-node (insert-upper-bound x p ub) lb (insert-bst x t) s
... | EQ p = bst-node ub lb t s
... | GT p = bst-node ub (insert-lower-bound x p lb) t (insert-bst x s)
