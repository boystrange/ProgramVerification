---
---

```agda
module QuickSort where

open import Unit
open import Nat
open import Product
open import Sum
open import Equality
open import List
open import List.Properties
open import LessThan
open import Permutation
open import Logic
open import Bool
open import Logic

variable A : Set

infix 4 _≼_ _≼*_ _*≼_

-- guardare lezioni su overloading di Peter Selinger
postulate
  _≼_       : A -> A -> Set
  ≼total    : (x y : A) -> x ≼ y ∨ y ≼ x
  ≼refl     : (x : A) -> x ≼ x
  ≼antisymm : (x y : A) -> x ≼ y -> y ≼ x -> x == y
  ≼trans    : {x y z : A} -> x ≼ y -> y ≼ z -> x ≼ z

_≼*_ : A -> List A -> Set
x ≼* xs = all (x ≼_) xs

_*≼_ : List A -> A -> Set
xs *≼ x = all (_≼ x) xs

partition : (x : A) (xs : List A) -> ∃[ ys ] ∃[ zs ] xs # ys ++ zs × ys *≼ x × x ≼* zs
partition x [] = [] , [] , #refl , <> , <>
partition x (u :: xs) with ≼total x u | partition x xs
... | left  x≼u | ys , zs , π , py , pz =
  ys , (u :: zs) , (#trans (#cong π) #push) , py , x≼u , pz
... | right u≼x | ys , zs , π , py , pz =
  u :: ys , zs , #cong π , (u≼x , py) , pz

sorted : List A -> Set
sorted [] = ⊤
sorted (x :: xs) = (x ≼* xs) × sorted xs

sorted-++ : {z : A} {xs ys : List A} -> sorted xs -> xs *≼ z -> z ≼* ys -> sorted ys -> sorted (xs ++ z :: ys)
sorted-++ {xs = []} p xs≼z z≼ys q = z≼ys , q
sorted-++ {_} {z} {xs = x :: xs} (x≼xs , p) (x≼z , xs≼z) z≼ys q =
  all-++ (x ≼_) x≼xs (x≼z , all-all (z ≼_) (x ≼_) (≼trans x≼z) z≼ys) , sorted-++ p xs≼z z≼ys q

{-# TERMINATING #-}
nt-quick-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ sorted ys
nt-quick-sort [] = [] , #refl , <>
nt-quick-sort (x :: xs) with partition x xs
... | ys , zs , π , py , pz with nt-quick-sort ys | nt-quick-sort zs
... | ys' , πy , sys | zs' , πz , szs =
  let π' = #begin
             x :: xs         #⟨ #cong π ⟩
             x :: ys ++ zs   #⟨ #cong (#cong++l πy) ⟩
             x :: ys' ++ zs  #⟨ #cong (#cong++r πz) ⟩
             x :: ys' ++ zs' #⟨ #push ⟩
             ys' ++ x :: zs'
           #end in
  (ys' ++ x :: zs' , π' , sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs)

lemma : {n : ℕ} {xs ys zs : List A} -> xs # ys ++ zs -> length xs <= n -> length ys <= n ∧ length zs <= n
lemma {xs = xs} {ys} {zs} π bound = <=split+ (subst (λ x -> x <= _) eq bound)
  where
    eq : length xs == length ys + length zs
    eq = begin
           length xs         ==⟨ #length π ⟩
           length (ys ++ zs) ==⟨ ++-length ys zs ⟩
           length ys + length zs
         end

quick-sort : {n : ℕ} (xs : List A) -> length xs <= n -> ∃[ ys ] xs # ys ∧ sorted ys
quick-sort [] _ = [] , #refl , <>
quick-sort (x :: xs) (succ T) with partition x xs
... | ys , zs , π , py , pz with lemma π T
... | Ty , Tz with quick-sort ys Ty | quick-sort zs Tz
... | ys' , πy , sys | zs' , πz , szs =
  let π' = #begin
             x :: xs         #⟨ #cong π ⟩
             x :: ys ++ zs   #⟨ #cong (#cong++l πy) ⟩
             x :: ys' ++ zs  #⟨ #cong (#cong++r πz) ⟩
             x :: ys' ++ zs' #⟨ #push ⟩
             ys' ++ x :: zs'
           #end in
  (ys' ++ x :: zs' , π' , sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs)
```
