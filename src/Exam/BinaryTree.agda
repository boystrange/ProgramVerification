module Exam.BinaryTree where

open import Library.Nat
open import Library.List
open import Library.List.Properties
open import Library.Equality
open import Library.Equality.Reasoning

data Tree (A : Set) : Set where
  leaf : Tree A
  node : A -> Tree A -> Tree A -> Tree A

size : {A : Set} -> Tree A -> ℕ
size leaf = 0
size (node _ t s) = succ (size t + size s)

depth : {A : Set} -> Tree A -> ℕ
depth leaf = 0
depth (node _ t s) = succ (max (depth t) (depth s))

elements : {A : Set} -> Tree A -> List A
elements leaf = []
elements (node x t s) = x :: elements t ++ elements s

size-elements : {A : Set} (t : Tree A) -> size t == length (elements t)
size-elements leaf = refl
size-elements (node x t s) =
  begin
    size (node x t s) ==⟨ refl ⟩
    succ (size t + size s) ==⟨ cong (\u -> succ (u + size s)) (size-elements t) ⟩
    succ (length (elements t) + size s) ==⟨ cong (\u -> succ (length (elements t) + u)) (size-elements s) ⟩
    succ (length (elements t) + length (elements s)) ==⟨ cong succ (symm (++-length (elements t) (elements s))) ⟩
    succ (length (elements t ++ elements s)) ==⟨ refl ⟩
    length (elements (node x t s))
  end
