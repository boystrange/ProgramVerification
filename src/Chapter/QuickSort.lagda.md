---
---

```agda
import TotalOrder

module Chapter.QuickSort (A : Set) (ord : TotalOrder.TotalOrder A) where

open import Unit
open import Nat
open import Product
open import Sum
open import Equality
open import Equality.Reasoning
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

open import WellFounded

infix 4 _<='_ _<'_

data _<='_ : ℕ -> ℕ -> Set where
  refl : {n : ℕ}   -> n <=' n
  succ : {m n : ℕ} -> m <=' n -> m <=' succ n

_<'_ : ℕ -> ℕ -> Set
x <' y = succ x <=' y

zero<=' : {x : ℕ} -> 0 <=' x
zero<=' {zero}   = refl
zero<=' {succ x} = succ zero<='

succ<=' : {x y : ℕ} -> x <=' y -> succ x <=' succ y
succ<=' refl     = refl
succ<=' (succ p) = succ (succ<=' p)

<=to<=' : {x y : ℕ} -> x <= y -> x <=' y
<=to<=' zero     = zero<='
<=to<=' (succ p) = succ<=' (<=to<=' p)

<='to<= : {x y : ℕ} -> x <=' y -> x <= y
<='to<= refl = le-refl
<='to<= (succ p) = <=-succ (<='to<= p)

accessible<' : (x y : ℕ) -> y <' x -> Accessible _<'_ y
accessible<' (succ y) _ refl      = acc (accessible<' y)
accessible<' (succ y) z (succ lt) = accessible<' y z lt

well-founded-lt' : WellFounded _<'_
well-founded-lt' x = acc (accessible<' x)

infix 4 _≺_

measure : {A B : Set} (_<A_ : A -> A -> Set) (_<B_ : B -> B -> Set)
          (f : A -> B) ->
          ({x y : A} -> x <A y -> f x <B f y) ->
          (x : A) -> Accessible _<B_ (f x) -> Accessible _<A_ x
measure _<A_ _<B_ f m x (acc g) =
  acc λ y lt -> measure _<A_ _<B_ f m y (g (f y) (m lt))

well-founded-m : {A B : Set} (_<A_ : A -> A -> Set) (_<B_ : B -> B -> Set)
                 (f : A -> B) ->
               ({x y : A} -> x <A y -> f x <B f y) ->
               WellFounded _<B_ -> WellFounded _<A_
well-founded-m _<A_ _<B_ f m wf x = measure _<A_ _<B_ f m x (wf (f x))

data _≺_ : List A -> List A -> Set where
  ≺-nil  : {x : A} {xs : List A} -> [] ≺ (x :: xs)
  ≺-cons : {x y : A} {xs ys : List A} -> xs ≺ ys -> (x :: xs) ≺ (y :: ys)

lemman : {xs ys : List A} -> xs ≺ ys -> length xs < length ys
lemman ≺-nil = succ zero
lemman (≺-cons p) = succ (lemman p)

lemman' : {xs ys : List A} -> xs ≺ ys -> length xs <' length ys
lemman' p = <=to<=' (lemman p)

lemmax : {xs ys : List A} {y : A} -> xs ≺ ys -> xs ≺ y :: ys
lemmax {[]} p = ≺-nil
lemmax {x :: xs} (≺-cons p) = ≺-cons (lemmax p)

well-founded-≺ : WellFounded _≺_
well-founded-≺ = well-founded-m _≺_ _<'_ length lemman' well-founded-lt'

permutation≺ : {xs ys zs : List A} -> xs # ys -> xs ≺ zs -> ys ≺ zs
permutation≺ #refl lt = lt
permutation≺ #swap (≺-cons (≺-cons lt)) = ≺-cons (≺-cons lt)
permutation≺ (#cong π) (≺-cons lt) = ≺-cons (permutation≺ π lt)
permutation≺ (#trans π π₁) lt = permutation≺ π₁ (permutation≺ π lt)

append≺ : {xs ys zs : List A} -> (xs ++ ys) ≺ zs -> (xs ≺ zs) ∧ (ys ≺ zs)
append≺ {[]}      {[]}     {_ :: _} ≺-nil = ≺-nil , ≺-nil
append≺ {[]}      {_ :: _} {_ :: _} (≺-cons p) = ≺-nil , ≺-cons p
append≺ {x :: xs} {ys}     {_ :: _} (≺-cons p) with append≺ p
... | px , py = ≺-cons px , lemmax py


```
