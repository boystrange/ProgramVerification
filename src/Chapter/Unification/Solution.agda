module Chapter.Unification.Solution where

open import Fun
open import Unit
open import Nat hiding (_-_)
open import Nat.Properties
open import List hiding ([_])
open import Logic
open import Equality
open import Equality.Reasoning
open import Product
open import Sum

open import Chapter.Unification.Domain
open import Chapter.Unification.Core
open import Chapter.Unification.Reduction

lemma-apply : (ρ σ : Substitution) (t : Term) -> apply (ρ · σ) t == (apply ρ ∘ apply σ) t
lemma-apply ρ σ (var i) = refl
lemma-apply ρ σ (t => s) rewrite lemma-apply ρ σ t | lemma-apply ρ σ s = refl

lemma-apply' : (i : Var) (t s : Term) -> i ∉ vars t -> apply (i >-> s) t == t
lemma-apply' i (var j) s i∉t with i =? j
... | yes refl = absurd (i∉t refl)
... | no x = refl
lemma-apply' i (t1 => t2) s i∉t rewrite lemma-apply' i t1 s (λ I → i∉t (left I)) |
                                        lemma-apply' i t2 s λ I -> i∉t (right I) = refl

lemma-singleton : (i : Var) (t : Term) -> (i >-> t) i == t
lemma-singleton i t with i =? i
... | yes refl = refl
... | no neq = absurd (neq refl)

lemma-singleton' : (i j : Var) (t : Term) -> j != i -> (i >-> t) j == var j
lemma-singleton' i j t neq with i =? j
... | yes refl = absurd (neq refl)
... | no x = refl

lemma-cod : (i j : Var) (σ : Substitution) -> j != i -> i ∉ cod σ -> i ∉ vars (σ j)
lemma-cod i j σ neq icod ivar = icod (j , lem , ivar)
  where
    lem : j ∈ dom σ
    lem eq with σ j
    ... | var k = neq (trans (var-injective (symm eq)) ivar)

swap-apply : (i : Var) (t : Term) (σ : Substitution) ->
  i ∉ cod σ -> i ∈ und σ -> (j : Var) -> (σ · (i >-> t)) j == ((i >-> apply σ t) · σ) j
swap-apply i t σ icod iund j with j =? i
... | yes refl =
  begin
    (σ · (i >-> t)) i               ==⟨⟩
    apply σ ((i >-> t) i)           ==⟨ cong (apply σ) (lemma-singleton i t) ⟩
    apply σ t                       ==⟨ symm (lemma-singleton i (apply σ t)) ⟩
    (i >-> apply σ t) i             ==⟨⟩
    apply (i >-> apply σ t) (var i) ==⟨ cong (apply (i >-> apply σ t)) (symm iund) ⟩
    apply (i >-> apply σ t) (σ i)   ==⟨⟩
    ((i >-> apply σ t) · σ) i
  end
... | no neq =
  begin
    (σ · (i >-> t)) j             ==⟨⟩
    apply σ ((i >-> t) j)         ==⟨ cong (apply σ) (lemma-singleton' i j t neq) ⟩
    apply σ (var j)               ==⟨⟩
    σ j                           ==⟨ symm (lemma-apply' i (σ j) (apply σ t) (lemma-cod i j σ neq icod)) ⟩
    apply (i >-> apply σ t) (σ j) ==⟨⟩
    ((i >-> apply σ t) · σ) j
  end

swap-apply' : (i : Var) (t s : Term) (σ : Substitution) ->
  i ∉ cod σ -> i ∈ und σ -> apply (σ · (i >-> t)) s == apply ((i >-> apply σ t) · σ) s
swap-apply' i t (var j) σ icod iund = swap-apply i t σ icod iund j
swap-apply' i t (s1 => s2) σ icod iund rewrite swap-apply' i t s1 σ icod iund |
                                               swap-apply' i t s2 σ icod iund = refl

lemma-apply-c : (i : Var) (t : Term) (σ : Substitution) (c : Constraint) ->
  i ∉ cod σ -> i ∈ und σ -> σ |>c c -> (σ · (i >-> t)) |>c c
lemma-apply-c i t σ (s1 ~ s2) icod iund sc =
  begin
    apply (σ · (i >-> t)) s1 ==⟨ swap-apply' i t s1 σ icod iund ⟩
    apply ((i >-> apply σ t) · σ) s1 ==⟨ lemma-apply (i >-> apply σ t) σ s1 ⟩
    (apply (i >-> apply σ t) ∘ apply σ) s1 ==⟨⟩
    apply (i >-> apply σ t) (apply σ s1) ==⟨ cong (apply (i >-> apply σ t)) sc ⟩
    apply (i >-> apply σ t) (apply σ s2) ==⟨⟩
    (apply (i >-> apply σ t) ∘ apply σ) s2 ==⟨ symm (lemma-apply (i >-> apply σ t) σ s2) ⟩
    apply ((i >-> apply σ t) · σ) s2 ==⟨ symm (swap-apply' i t s2 σ icod iund) ⟩
    apply (σ · (i >-> t)) s2
  end

lemma-apply-cs : (i : Var) (t : Term) (σ : Substitution) (cs : Constraints) ->
  i ∉ cod σ -> i ∈ und σ -> σ |>cs cs -> (σ · (i >-> t)) |>cs cs
lemma-apply-cs i t σ [] icod iund ok = <>
lemma-apply-cs i t σ (c :: cs) icod iund (sc , ok) = lemma-apply-c i t σ c icod iund sc , lemma-apply-cs i t σ cs icod iund ok

Tight : Substitution -> Constraints -> Set
Tight σ cs = (i : Var) -> i ∉ vars-cs cs -> i ∈ und σ ∧ i ∉ cod σ

lemma-apply-t : (i : Var) (s t : Term) -> i ∉ vars t -> apply (i >-> s) t == t
lemma-apply-t i s (var j) i∉t with i =? j
... | yes refl = absurd (i∉t refl)
... | no x = refl
lemma-apply-t i s (t1 => t2) i∉t rewrite lemma-apply-t i s t1 (λ I → i∉t (left I)) |
                                         lemma-apply-t i s t2 λ I -> i∉t (right I) = refl

empty-tight : Tight empty-substitution []
empty-tight i i∉cs = refl , lem
  where
    lem : i ∉ cod empty-substitution
    lem (j , jdom , refl) = jdom refl

und-compose : (σ ρ : Substitution) (i : Var) -> i ∈ und σ -> i ∈ und ρ -> i ∈ und (σ · ρ)
und-compose σ ρ i p q =
  begin
    (σ · ρ) i ==⟨⟩
    apply σ (ρ i) ==⟨ cong (apply σ) q ⟩
    apply σ (var i) ==⟨⟩
    σ i ==⟨ p ⟩
    var i
  end

stupid-lemma-6 : (i j : Var) (σ : Substitution) ->
  σ i == var i -> j ∈ vars (σ i) -> i == j
stupid-lemma-6 i j σ eq1 jin rewrite eq1 = jin

lemma-apply-und : (j : Var) (σ : Substitution) (t : Term) ->
  j ∈ und σ -> j ∈ vars (apply σ t) -> j ∈ cod σ ∨ j ∈ vars t
lemma-apply-und j σ (var i) jund J with i =? j
... | yes refl = right refl
... | no i!=j = left (i , (λ { p -> i!=j (stupid-lemma-6 i j σ p J) }) , J)

lemma-apply-und j σ (t => s) jund (left J) with lemma-apply-und j σ t jund J
... | left K = left K
... | right K = right (left K)
lemma-apply-und j σ (t => s) jund (right J) with lemma-apply-und j σ s jund J
... | left K = left K
... | right K = right (right K)

lemma-cod-compose : (i j : Var) (σ : Substitution) (t : Term) ->
  j ∈ und σ -> j ∈ cod (σ · (i >-> t)) -> j ∈ cod σ ∨ j ∈ vars t
lemma-cod-compose i j σ t jund (k , kdom , kin) with i =? k
... | yes refl = lemma-apply-und j σ t jund kin
... | no neq = left (k , kdom , kin)

lemma-cod-compose' : (i j : Var) (σ : Substitution) (t : Term) ->
  j ∈ und σ -> j ∉ cod σ -> j ∉ vars t -> j ∉ cod (σ · (i >-> t))
lemma-cod-compose' i j σ t jund jcod jin p with lemma-cod-compose i j σ t jund p
... | left x = jcod x
... | right x = jin x

lemma-tight : (i : Var) (t : Term) (σ : Substitution) (cs : Constraints) ->
  Tight σ cs -> i ∉ vars t -> i ∉ vars-cs cs -> Tight (σ · (i >-> t)) ((var i ~ t) :: cs)
lemma-tight i t σ cs tight i∉t i∉cs j J =
  let j∉c , j∉cs = union-not-in j (vars-c (var i ~ t)) (vars-cs cs) J in
  let j∉i , j∉t  = union-not-in j (vars (var i)) (vars t) j∉c in
  let jund , jcod = tight j j∉cs in
  und-compose σ (i >-> t) j jund (lemma-singleton' i j t (not-in-not-equal i j j∉i)) ,
  lemma-cod-compose' i j σ t jund jcod j∉t

solve : (cs : Constraints) -> SolvedConstraints cs -> ∃[ σ ] σ |>cs cs ∧ Tight σ cs
solve [] sol = empty-substitution , <> , empty-tight
solve ((var i ~ t) :: cs) (i∉t , i∉cs , sol) with solve cs sol
... | σ , ok , tight =
  let eq = begin
             (σ · (i >-> t)) i             ==⟨⟩
             apply σ ((i >-> t) i)         ==⟨ cong (apply σ) (lemma-singleton i t) ⟩
             apply σ t                     ==⟨ cong (apply σ) (symm (lemma-apply-t i t t i∉t)) ⟩
             apply σ (apply (i >-> t) t)   ==⟨⟩
             (apply σ ∘ apply (i >-> t)) t ==⟨ symm (lemma-apply σ (i >-> t) t) ⟩
             apply (σ · (i >-> t)) t
           end
  in
  let iund , icod = tight i i∉cs in
  (σ · (i >-> t)) ,
  (eq , lemma-apply-cs i t σ cs icod iund ok) ,
  lemma-tight i t σ cs tight i∉t i∉cs
