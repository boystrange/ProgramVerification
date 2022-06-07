module Chapter.Unification.Core where

open import Nat
open import Nat.Properties
open import Equality
open import Equality.Reasoning
open import Logic
open import List hiding ([_])

open import Chapter.Unification.Domain

data Term : Set where
  var : Var -> Term
  _=>_ : Term -> Term -> Term

data Constraint : Set where
  _~_ : Term -> Term -> Constraint

Constraints : Set
Constraints = List (Constraint)

Substitution : Set
Substitution = Var -> Term

vars : Term -> Domain
vars (var i)  = [ i ]
vars (t => s) = vars t ∪ vars s

vars-l : Constraint -> Domain
vars-l (t ~ _) = vars t

vars-r : Constraint -> Domain
vars-r (_ ~ s) = vars s

vars-c : Constraint -> Domain
vars-c c = vars-l c ∪ vars-r c

vars-cs : Constraints -> Domain
vars-cs [] = ∅
vars-cs (c :: cs) = vars-c c ∪ vars-cs cs

vars-ls : Constraints -> Domain
vars-ls [] = ∅
vars-ls (c :: cs) = vars-l c ∪ vars-ls cs

vars-rs : Constraints -> Domain
vars-rs [] = ∅
vars-rs (c :: cs) = vars-r c ∪ vars-rs cs

empty-substitution : Substitution
empty-substitution = var

und : Substitution -> Domain
und σ i = σ i == var i

dom : Substitution -> Domain
dom σ i = σ i != var i

cod : Substitution -> Domain
cod σ i = ∃[ j ] j ∈ dom σ ∧ i ∈ vars (σ j)

_>->_ : Var -> Term -> Substitution
_>->_ i t j with i =? j
... | yes refl = t
... | no  _    = var j

apply : Substitution -> Term -> Term
apply σ (var i) = σ i
apply σ (t => s) = apply σ t => apply σ s

_·_ : Substitution -> Substitution -> Substitution
σ · ρ = λ i -> apply σ (ρ i)

-- RINOMINARE IN APPLY-...

subst-c : Substitution -> Constraint -> Constraint
subst-c σ (t ~ s) = apply σ t ~ apply σ s

subst-cs : Substitution -> Constraints -> Constraints
subst-cs _ [] = []
subst-cs σ (c :: cs) = subst-c σ c :: subst-cs σ cs

_|>c_ : Substitution -> Constraint -> Set
σ |>c (t ~ s) = apply σ t == apply σ s

_|>cs_ : Substitution -> Constraints -> Set
σ |>cs cs = all (σ |>c_) cs

very-stupid-lemma : (a b c d e : ℕ) -> (a + b + (c + d + e)) == (a + c + (b + d + e))
very-stupid-lemma a b c d e =
  begin
    a + b + (c + d + e) ==⟨ +-associative (a + b) (c + d) e ⟩
    a + b + (c + d) + e ==⟨ cong (_+ e) (symm (+-associative a b (c + d))) ⟩
    a + (b + (c + d)) + e ==⟨ cong (λ x -> a + x + e) (+-associative b c d) ⟩
    a + (b + c + d) + e ==⟨ cong (λ x -> a + (x + d) + e) (+-commutative b c) ⟩
    a + (c + b + d) + e ==⟨ cong (λ x -> a + x + e) (symm (+-associative c b d)) ⟩
    a + (c + (b + d)) + e ==⟨ cong (_+ e) (+-associative a c (b + d)) ⟩
    a + c + (b + d) + e ==⟨ symm (+-associative (a + c) (b + d) e) ⟩
    a + c + (b + d + e)
  end

