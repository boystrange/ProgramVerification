module Chapter.Unification.Reduction where

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

data State : Set where
  ⟨_,_⟩ : (cs cs' : Constraints) -> State

data _~>_ : State -> State -> Set where
  nop : {cs cs' : Constraints} {i : Var} ->
        ⟨ cs , (var i ~ var i) :: cs' ⟩ ~> ⟨ cs , cs' ⟩
  sub : {cs cs' : Constraints} (i : Var) (t : Term) ->
        (i∉t : i ∉ vars t) ->
        ⟨ cs , (var i ~ t) :: cs' ⟩ ~> ⟨ (var i ~ t) :: subst-cs (i >-> t) cs , subst-cs (i >-> t) cs' ⟩
  arr : {cs cs' : Constraints} {t s u v : Term} ->
        ⟨ cs , ((t => s) ~ (u => v)) :: cs' ⟩ ~> ⟨ cs , (t ~ u) :: (s ~ v) :: cs' ⟩

data _~~>_ : State -> State -> Set where
  here : {S T : State} -> S ~> T -> S ~~> T
  swap : {cs cs' : Constraints} {t s : Term} {T : State} ->
         ⟨ cs , (s ~ t) :: cs' ⟩ ~~> T -> ⟨ cs , (t ~ s) :: cs' ⟩ ~~> T

SolvedConstraints : Constraints -> Set
SolvedConstraints [] = ⊤
SolvedConstraints ((var i ~ t) :: cs) = i ∉ vars t ∧ i ∉ vars-cs cs ∧ SolvedConstraints cs
SolvedConstraints (((_ => _) ~ _) :: _) = ⊥

WellFormed : State -> Set
WellFormed ⟨ cs , cs' ⟩ = SolvedConstraints cs ∧ vars-ls cs # vars-cs cs'

lemma-t : (i : Var) (t s : Term) -> i ∉ vars t -> i ∉ vars (apply (i >-> t) s)
lemma-t i t (var j) i∉t I with i =? j
... | yes refl = i∉t I
... | no x = x (symm I)
lemma-t i t (s1 => s2) i∉t (left I) = lemma-t i t s1 i∉t I
lemma-t i t (s1 => s2) i∉t (right I) = lemma-t i t s2 i∉t I

lemma-c : (i : Var) (t : Term) (c : Constraint) -> i ∉ vars t -> i ∉ vars-c (subst-c (i >-> t) c)
lemma-c i t (s1 ~ s2) i∉t (left I) = lemma-t i t s1 i∉t I
lemma-c i t (s1 ~ s2) i∉t (right I) = lemma-t i t s2 i∉t I

lemma-cs : (i : Var) (t : Term) (cs : Constraints) -> i ∉ vars t -> i ∉ vars-cs (subst-cs (i >-> t) cs)
lemma-cs i t [] i∉t I = I
lemma-cs i t (c :: cs) i∉t (left I) = lemma-c i t c i∉t I
lemma-cs i t (c :: cs) i∉t (right I) = lemma-cs i t cs i∉t I

lemma-subst-t : (i : Var) (t s : Term) -> i ∉ vars t ->
  vars (apply (i >-> t) s) ⊆ (vars s ∪ vars t)
lemma-subst-t i t (var j) i∉t {k} K with i =? j
... | yes refl = right K
... | no x = left K
lemma-subst-t i t (s1 => s2) i∉t (left K) with lemma-subst-t i t s1 i∉t K
... | left K' = left (left K')
... | right K' = right K'
lemma-subst-t i t (s1 => s2) i∉t (right K) with lemma-subst-t i t s2 i∉t K
... | left K' = left (right K')
... | right K' = right K'

lemma-subst-c : (i : Var) (t : Term) (c : Constraint) -> i ∉ vars t ->
  vars-c (subst-c (i >-> t) c) ⊆ (vars-c c ∪ vars t)
lemma-subst-c i t (s1 ~ s2) i∉t (left K) with lemma-subst-t i t s1 i∉t K
... | left K' = left (left K')
... | right K' = right K'
lemma-subst-c i t (s1 ~ s2) i∉t (right K) with lemma-subst-t i t s2 i∉t K
... | left K' = left (right K')
... | right K' = right K'

lemma-subst-cs : (i : Var) (t : Term) (cs : Constraints) -> i ∉ vars t ->
  vars-cs (subst-cs (i >-> t) cs) ⊆ (vars-cs cs ∪ vars t)
lemma-subst-cs i t (c :: cs) i∉t (left K) with lemma-subst-c i t c i∉t K
... | left K' = left (left K')
... | right K' = right K'
lemma-subst-cs i t (c :: cs) i∉t (right K) with lemma-subst-cs i t cs i∉t K
... | left K' = left (right K')
... | right K' = right K'

stupid-lemma4 : (i j k : Var) (t : Term) -> [ k ] # [ i ] -> j ∈ vars ((i >-> t) k) -> k == j
stupid-lemma4 i j k t k#i inc with i =? k
... | yes refl = absurd (k#i k (refl , refl))
... | no neq = inc

lemma-subst-ls : (i : Var) (t : Term) (cs : Constraints) -> SolvedConstraints cs ->
  vars-ls cs # [ i ] -> vars-ls (subst-cs (i >-> t) cs) ⊆ vars-ls cs
lemma-subst-ls i t ((var k ~ s) :: cs) (k∉s , k∉cs , sol) cs#i {j} (left J) =
  let k#i , _ = disjoint-split-l cs#i in
  left (stupid-lemma4 i j k t k#i J)
lemma-subst-ls i t ((var k ~ s) :: cs) (k∉s , k∉cs , sol) cs#i {j} (right J) =
  let _ , cs#i' = disjoint-split-l cs#i in
  right (lemma-subst-ls i t cs sol cs#i' J)

lemma1 : (cs : Constraints) {i : Var} {t : Term} ->
  SolvedConstraints cs -> i ∉ vars-ls cs -> i ∉ vars t -> i ∉ vars-cs (subst-cs (i >-> t) cs)
lemma1 ((var j ~ s) :: cs) {i} sol p q (left (left I)) with i =? j
... | yes refl = q I
... | no x = p (left I)
lemma1 ((var j ~ s) :: cs) {i} {t} sol p q (left (right I)) = lemma-t i t s q I
lemma1 ((var j ~ s) :: cs) (_ , _ , sol) p q (right I) =
  lemma1 cs sol (λ I' → p (right I')) q I

stupid-lemma2 : (j : Var) (t s : Term) -> [ j ] # vars t -> j ∉ vars s -> j ∉ (vars s ∪ vars t)
stupid-lemma2 j t s j#t j∉s (left J) = j∉s J
stupid-lemma2 j t s j#t j∉s (right J) = j#t j (refl , J)

stupid-lemma3 : (j : Var) (t : Term) (cs : Constraints) -> [ j ] # vars t -> j ∉ vars-cs cs -> j ∉ (vars-cs cs ∪ vars t)
stupid-lemma3 j t cs j#t j∉cs (left J) = j∉cs J
stupid-lemma3 j t cs j#t j∉cs (right J) = j#t j (refl , J)

lemma4 : (cs : Constraints) {i : Var} {t : Term} ->
  SolvedConstraints cs -> i ∉ vars t -> vars-ls cs # [ i ] -> vars-ls cs # vars t -> SolvedConstraints (subst-cs (i >-> t) cs)
lemma4 [] sol i∉t cs#i cs#t = <>
lemma4 ((var j ~ s) :: cs) {i} {t} (j∉s , j∉cs , sol) i∉t cs#i cs#t with i =? j
... | yes refl = absurd (cs#i j (left refl , refl))
... | no x =
  let j#i , cs#i' = disjoint-split-l {[ j ]} {vars-ls cs} {[ i ]} cs#i in
  let j#t , cs#t' = disjoint-split-l {[ j ]} {vars-ls cs} {vars t} cs#t in
  contrapositive (lemma-subst-t i t s i∉t) (stupid-lemma2 j t s j#t j∉s) ,
  contrapositive (lemma-subst-cs i t cs i∉t) (stupid-lemma3 j t cs j#t j∉cs) ,
  lemma4 cs {i} sol i∉t
    (λ { k (k∈cs , refl) → cs#i k (right k∈cs , refl) })
    λ { k (k∈cs , k∈t) → cs#t k (right k∈cs , k∈t)}

stupid-lemma : (cs : Constraints) (i : Var) (t : Term) -> (vars-cs cs ∪ vars t) ⊆ (vars-c (var i ~ t) ∪ vars-cs cs)
stupid-lemma cs i t (left K) = right K
stupid-lemma cs i t (right K) = left (right K)

wf : {S T : State} -> S ~> T -> WellFormed S -> WellFormed T
wf nop (sol , dis) = sol , λ i (I , J) -> dis i (I , right J)
wf (sub {cs = cs} {cs'} i t i∉t) (sol , dis) =
  let dis1 , cs#cs' = disjoint-split-r {vars-ls cs} {vars-c (var i ~ t)} {vars-cs cs'} dis in
  let cs#i , cs#t   = disjoint-split-r {vars-ls cs} {[ i ]} {vars t} dis1 in
  (i∉t , lemma1 _ sol (λ I → dis i (I , left (left refl))) i∉t , lemma4 cs sol i∉t cs#i cs#t) ,
  disjoint-union
    (λ { j (refl , J) → lemma-cs j t cs' i∉t J})
    λ { k (k∈cs , k∈cs') → dis k (lemma-subst-ls i t cs sol cs#i k∈cs ,
      let res = lemma-subst-cs i t cs' i∉t k∈cs' in
      stupid-lemma cs' i t res)}
wf arr (sol , dis) = sol , λ { i (I , left (left J)) → dis i (I , left (left (left J)))
                             ; i (I , left (right J)) → dis i (I , left (right (left J)))
                             ; i (I , right (left (left J))) → dis i (I , left (left (right J)))
                             ; i (I , right (left (right J))) → dis i (I , left (right (right J)))
                             ; i (I , right (right J)) → dis i (I , right J) }

wf' : {S T : State} -> S ~~> T -> WellFormed S -> WellFormed T
wf' (here red) w = wf red w
wf' (swap red) (sol , dis) =
  wf' red (sol , λ { i (I , left (left  J)) → dis i (I , left (right J))
                   ; i (I , left (right J)) → dis i (I , left (left J))
                   ; i (I , right J) -> dis i (I , right J) })

_|>_ : Substitution -> State -> Set
σ |> ⟨ cs , cs' ⟩ = σ |>cs cs ∧ σ |>cs cs'

var-injective : {i j : Var} -> var i == var j -> i == j
var-injective refl = refl

arr-injective : {t s u v : Term} -> (t => s) == (u => v) -> t == u ∧ s == v
arr-injective refl = refl , refl

forward-t : {σ : Substitution} {i : Var} (t s : Term) ->
  σ i == apply σ t -> apply σ s == apply σ (apply (i >-> t) s)
forward-t {i = i} t (var k) eq with k =? i
... | yes refl with i =? i
... | yes refl = eq
... | no x = refl
forward-t {i = i} t (var k) eq | no x with i =? k
... | yes refl = eq
... | no _ = refl
forward-t t (s1 => s2) eq with forward-t t s1 eq | forward-t t s2 eq
... | eq1 | eq2 rewrite eq1 | eq2 = refl

forward-c : {σ : Substitution} {i : Var} {t : Term} (c : Constraint) ->
  σ i == apply σ t -> σ |>c c -> σ |>c subst-c (i >-> t) c
forward-c {t = t} (s1 ~ s2) eq sol with forward-t t s1 eq | forward-t t s2 eq
... | eq1 | eq2 rewrite eq1 | eq2 = sol

backward-c : {σ : Substitution} {i : Var} {t : Term} (c : Constraint) ->
  σ i == apply σ t -> σ |>c (subst-c (i >-> t) c) -> σ |>c c
backward-c {t = t} (t1 ~ t2) eq sol rewrite forward-t t t1 eq |
                                            forward-t t t2 eq = sol

forward-cs : {σ : Substitution} {i : Var} {t : Term} (cs : Constraints) ->
  σ i == apply σ t -> σ |>cs cs -> σ |>cs (subst-cs (i >-> t) cs)
forward-cs [] eq <> = <>
forward-cs (c :: cs) eq (sol , sols) = forward-c c eq sol , forward-cs cs eq sols

backward-cs : {σ : Substitution} {i : Var} {t : Term} (cs : Constraints) ->
  σ i == apply σ t -> σ |>cs (subst-cs (i >-> t) cs) -> σ |>cs cs
backward-cs [] eq sol = <>
backward-cs (c :: cs) eq (s , sol) = backward-c _ eq s , backward-cs _ eq sol

forward : {S T : State} {σ : Substitution} -> S ~> T -> σ |> S -> σ |> T
forward nop (sol , _ , sol') = sol , sol'
forward (sub i t i∉t) (sol , eq , sol') =
  (eq , forward-cs _ eq sol) , forward-cs _ eq sol'
forward arr (sol , eq , sol') with arr-injective eq
... | eq1 , eq2 = sol , eq1 , eq2 , sol'

forward' : {S T : State} {σ : Substitution} -> S ~~> T -> σ |> S -> σ |> T
forward' (here red) sol = forward red sol
forward' (swap red) (sol , eq , sol') = forward' red (sol , symm eq , sol')

backward : {S T : State} {σ : Substitution} -> S ~> T -> σ |> T -> σ |> S
backward nop (sol , sol') = sol , refl , sol'
backward (sub i t i∉t) ((eq , sol) , sol') =
  backward-cs _ eq sol , eq , backward-cs _ eq sol'
backward arr (sol , eq1 , eq2 , sol') rewrite eq1 | eq2 = sol , refl , sol'

backward' : {S T : State} {σ : Substitution} -> S ~~> T -> σ |> T -> σ |> S
backward' (here red) sol = backward red sol
backward' (swap red) sol with backward' red sol
... | sol , eq , sol' = sol , symm eq , sol'
