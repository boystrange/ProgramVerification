---
---

```agda
import TotalOrder

module Chapter.QuickSort (A : Set) (ord : TotalOrder.TotalOrder A) where

open import Unit
open import Nat
open import Nat.Properties
open import Product
open import Sum
open import Equality
open import List
open import List.Sorted A ord
open import List.Properties
open import List.Permutation
open import LessThan
open import LessThan.Reasoning
open import Logic
open import Bool
open import Logic

open TotalOrder.TotalOrder ord

partition : (x : A) (xs : List A) -> ∃[ ys ] ∃[ zs ] xs # ys ++ zs ∧ ys *≼ x ∧ x ≼* zs
partition x [] = [] , [] , #refl , <> , <>
partition x (u :: xs) with ≼total x u | partition x xs
... | left  x≼u | ys , zs , π , py , pz =
  ys , u :: zs , #trans (#cong π) #push , py , x≼u , pz
... | right u≼x | ys , zs , π , py , pz =
  u :: ys , zs , #cong π , (u≼x , py) , pz

sorted-++ : {z : A} {xs ys : List A} -> Sorted xs -> xs *≼ z -> z ≼* ys -> Sorted ys -> Sorted (xs ++ z :: ys)
sorted-++ {xs = []} p xs≼z z≼ys q = z≼ys , q
sorted-++ {z} {xs = x :: xs} (x≼xs , p) (x≼z , xs≼z) z≼ys q =
  all-++ (x ≼_) x≼xs (x≼z , all-all (z ≼_) (x ≼_) (≼trans x≼z) z≼ys) ,
  sorted-++ p xs≼z z≼ys q

{-# TERMINATING #-}
nt-quick-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
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
  ys' ++ x :: zs' , π' ,
  sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs

open import WellFounded
open import LessThan.Alternative

accessible<' : (x y : ℕ) -> y <' x -> Accessible _<'_ y
accessible<' (succ y) _ refl      = acc (accessible<' y)
accessible<' (succ y) z (succ lt) = accessible<' y z lt

well-founded-lt' : WellFounded _<'_
well-founded-lt' x = acc (accessible<' x)

infix 4 _⊑_ _⊏_

_⊑_ : List A -> List A -> Set
xs ⊑ ys = length xs <= length ys

_⊏_ : List A -> List A -> Set
xs ⊏ ys = length xs < length ys

well-founded-⊏ : WellFounded _⊏_
well-founded-⊏ = well-founded-m _⊏_ _<'_ length <=to<=' well-founded-lt'

lemma-⊑ : (xs ys zs : List A) -> xs # ys ++ zs -> ys ⊑ xs
lemma-⊑ xs ys zs π =
  begin
    length ys             <=⟨ le-plus (length ys) (length zs) ⟩
    length ys + length zs ==⟨ symm (++-length ys zs) ⟩
    length (ys ++ zs)     ==⟨ symm (#length π) ⟩
    length xs
  end

quick-sort-aux : (xs : List A) -> Accessible _⊏_ xs -> ∃[ ys ] xs # ys ∧ Sorted ys
quick-sort-aux [] _ = [] , #refl , <>
quick-sort-aux (x :: xs) (acc f) with partition x xs
... | ys , zs , π , py , pz with lemma-⊑ xs ys zs π |
                                 lemma-⊑ xs zs ys (#trans π (++-permutation ys zs))
... | ys⊑xs | zs⊑xs with quick-sort-aux ys (f ys (succ ys⊑xs)) |
                         quick-sort-aux zs (f zs (succ zs⊑xs))
... | ys' , πy , sys | zs' , πz , szs =
  let π' = #begin
             x :: xs         #⟨ #cong π ⟩
             x :: ys ++ zs   #⟨ #cong (#cong++l πy) ⟩
             x :: ys' ++ zs  #⟨ #cong (#cong++r πz) ⟩
             x :: ys' ++ zs' #⟨ #push ⟩
             ys' ++ x :: zs'
           #end in
  ys' ++ x :: zs' , π' , sorted-++ sys (#all (_≼ x) πy py) (#all (x ≼_) πz pz) szs

quick-sort : (xs : List A) -> ∃[ ys ] xs # ys ∧ Sorted ys
quick-sort xs = quick-sort-aux xs (well-founded-⊏ xs)
```
