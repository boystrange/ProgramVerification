
module Chapter.Unification.Domain where

open import Fun
open import Sum
open import Product
open import Equality
open import Logic
open import Nat hiding (_-_)

Var : Set
Var = ℕ

Domain : Set₁
Domain = Var -> Set

∅ : Domain
∅ = λ _ -> ⊥

[_] : Var -> Domain
[_] i j = i == j

_∈_ : Var -> Domain -> Set
_∈_ i X = X i

_∉_ : Var -> Domain -> Set
_∉_ i X = ¬ (X i)

_∪_ : Domain -> Domain -> Domain
X ∪ Y = λ i -> i ∈ X ∨ i ∈ Y

_∩_ : Domain -> Domain -> Domain
X ∩ Y = λ i -> i ∈ X ∧ i ∈ Y

_-_ : Domain -> Domain -> Domain
X - Y = λ i -> i ∈ X ∧ i ∉ Y

_⊆_ : Domain -> Domain -> Set
_⊆_ X Y = {i : Var} -> i ∈ X -> i ∈ Y

⊆-trans : {X Y Z : Domain} -> X ⊆ Y -> Y ⊆ Z -> X ⊆ Z
⊆-trans p q I = q (p I)

_⊊_ : Domain -> Domain -> Set
X ⊊ Y = (X ⊆ Y) ∧ (∃[ i ] i ∈ (Y - X))

complement : Domain -> Domain
complement X i = i ∉ X

empty : Domain -> Set
empty dom = (i : Var) -> i ∉ dom

_#_ : Domain -> Domain -> Set
X # Y = empty (X ∩ Y)

union-⊆-l : {X Y : Domain} -> X ⊆ (X ∪ Y)
union-⊆-l = left

union-⊆-r : {X Y : Domain} -> Y ⊆ (X ∪ Y)
union-⊆-r = right

union-in : {i : Var} {X : Domain} -> [ i ] ⊆ X -> i ∈ X
union-in inc = inc refl

union-split : {X Y Z : Domain} -> (X ∪ Y) ⊆ Z -> X ⊆ Z ∧ Y ⊆ Z
union-split inc = (inc ∘ left) , (inc ∘ right)

union-join : {X Y Z : Domain} -> X ⊆ Z -> Y ⊆ Z -> (X ∪ Y) ⊆ Z
union-join inc1 inc2 (left I) = inc1 I
union-join inc1 inc2 (right I) = inc2 I

disjoint-split-l : {X Y Z : Domain} -> (X ∪ Y) # Z -> (X # Z) ∧ (Y # Z)
disjoint-split-l dis = (λ i (I , J) → dis i (left I , J)) , λ i (I , J) → dis i (right I , J)

disjoint-split-r : {X Y Z : Domain} -> X # (Y ∪ Z) -> (X # Y) ∧ (X # Z)
disjoint-split-r dis = (λ i (I , J) → dis i (I , left J)) , λ i (I , J) → dis i (I , right J)

disjoint-union : {X Y Z : Domain} -> X # Z -> Y # Z -> (X ∪ Y) # Z
disjoint-union dis1 dis2 = λ { i (left X , Z) → dis1 i (X , Z)
                             ; i (right Y , Z) → dis2 i (Y , Z)}

disjoint-subset : {X Y Z : Domain} -> X ⊆ Y -> Y # Z -> X # Z
disjoint-subset inc dis = λ i (X , Z) → dis i (inc X , Z)

union-not-in : (i : Var) (X Y : Domain) -> i ∉ (X ∪ Y) -> i ∉ X ∧ i ∉ Y
union-not-in i X Y p = (p ∘ left) , (p ∘ right)

not-in-not-equal : (i j : Var) -> j ∉ [ i ] -> j != i
not-in-not-equal i .i j∉i refl = j∉i refl

