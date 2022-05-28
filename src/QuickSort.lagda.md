---
---

```agda
import TotalOrder

module QuickSort (A : Set) (ord : TotalOrder.TotalOrder A) where

open import Unit
open import Nat
open import Product
open import Sum
open import Equality
open import List
open import List.Sorted A ord
open import List.Properties
open import List.Permutation
open import LessThan
open import Logic
open import Bool
open import Logic

open TotalOrder.TotalOrder ord

partition : (x : A) (xs : List A) -> ∃[ ys ] ∃[ zs ] xs # ys ++ zs ∧ ys *≼ x ∧ x ≼* zs
partition x [] = [] , [] , #refl , <> , <>
partition x (u :: xs) with ≼total x u | partition x xs
... | left  x≼u | ys , zs , π , py , pz =
  ys , (u :: zs) , (#trans (#cong π) #push) , py , x≼u , pz
... | right u≼x | ys , zs , π , py , pz =
  u :: ys , zs , #cong π , (u≼x , py) , pz

sorted-++ : {z : A} {xs ys : List A} -> sorted xs -> xs *≼ z -> z ≼* ys -> sorted ys -> sorted (xs ++ z :: ys)
sorted-++ {xs = []} p xs≼z z≼ys q = z≼ys , q
sorted-++ {z} {xs = x :: xs} (x≼xs , p) (x≼z , xs≼z) z≼ys q =
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
