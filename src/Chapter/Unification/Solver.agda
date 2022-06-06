module Chapter.Unification.Solver where

open import Unit
open import Nat
open import Nat.Properties
open import Logic
open import List hiding ([_])
open import Product
open import Sum
open import Sigma
open import Equality
open import LessThan
open import LessThan.Reasoning
open import LessThan.Alternative
open import WellFounded

open import Chapter.Unification.Domain
open import Chapter.Unification.Core
open import Chapter.Unification.Reduction

postulate
  _∈?_ : (i : Var) (t : Term) -> Decidable (i ∈ vars t)
  size : Domain -> ℕ
  le-size : {X Y : Domain} -> size Y <= size (X ∪ Y)
  nat : Var -> ℕ

accessible<' : (x y : ℕ) -> y <' x -> Accessible _<'_ y
accessible<' (succ y) _ refl      = acc (accessible<' y)
accessible<' (succ y) z (succ lt) = accessible<' y z lt

well-founded-lt' : WellFounded _<'_
well-founded-lt' x = acc (accessible<' x)

Measure : Set
Measure = ℕ × ℕ

_<=²'_ : Measure -> Measure -> Set
(x , y) <=²' (u , v) = x <' u ∨ (x == u ∧ y <=' v)

_<²'_ : Measure -> Measure -> Set
(x , y) <²' (u , v) = x <' u ∨ (x == u ∧ y <' v)

accessible<²' : (p q : Measure) -> q <²' p -> Accessible _<²'_ q
accessible<²' (.(succ (fst q)) , _) q (left refl) = acc (accessible<²' q)
accessible<²' (succ x , y) q (left (succ lt)) = accessible<²' (x , y) q (left lt)
accessible<²' (x , succ y) (.x , u) (right (refl , refl)) = acc (accessible<²' (x , u))
accessible<²' (x , succ y) (.x , u) (right (refl , succ lt)) = accessible<²' (x , y) (x , u) (right (refl , lt))

well-founded<²' : WellFounded _<²'_
well-founded<²' p = acc (accessible<²' p)

size-t : Term -> ℕ
size-t (var _) = 1
size-t (t => s) = succ (size-t t + size-t s)

size-c : Constraint -> ℕ
size-c (t ~ s) = size-t t + size-t s

size-cs : Constraints -> ℕ
size-cs [] = 0
size-cs (c :: cs) = size-c c + size-cs cs

_<=²_ : Measure -> Measure -> Set
(x , y) <=² (u , v) = x < u ∨ (x == u ∧ y <= v)

_<²_ : Measure -> Measure -> Set
(x , y) <² (u , v) = x < u ∨ (x == u ∧ y < v)

measure-l : Constraints -> Constraints -> ℕ
measure-l cs cs' = size (vars-rs cs ∪ vars-cs cs')

measure-r : Constraints -> ℕ
measure-r cs = size-cs cs

measure : State -> Measure
measure ⟨ cs , cs' ⟩ = measure-l cs cs' , measure-r cs'

<=²to<=²' : {p q : Measure} -> p <=² q -> p <=²' q
<=²to<=²' (left le) = left (<=to<=' le)
<=²to<=²' (right (eq , le)) = right (eq , <=to<=' le)

_⊏_ : State -> State -> Set
S ⊏ T = measure S <² measure T

well-founded-⊏ : WellFounded _⊏_
well-founded-⊏ = well-founded-m _⊏_ _<²'_ measure <=²to<=²' well-founded<²'

make<²l : {x y u v : ℕ} -> x < u -> (x , y) <² (u , v)
make<²l = left

make<²r : {x y u v : ℕ} -> x == u -> y < v -> (x , y) <² (u , v)
make<²r eq lt = right (eq , lt)

make<² : {x y u v : ℕ} -> x <= u -> y < v -> (x , y) <² (u , v)
make<² {x} {_} {u} le lt with x =? u
... | yes eq = right (eq , lt)
... | no neq = left (le-ne-lt le neq)


postulate
  size-union-assoc : {X Y Z : Domain} -> size (X ∪ (Y ∪ Z)) == size (Y ∪ (X ∪ Z))

Stuck : State -> Set
Stuck ⟨ _ , [] ⟩ = ⊤
Stuck ⟨ _ , (var i ~ var _) :: _ ⟩ = ⊥
Stuck ⟨ _ , (var i ~ t@(_ => _)) :: _ ⟩ = i ∈ vars t
Stuck ⟨ _ , (t@(_ => _) ~ var i) :: _ ⟩ = i ∈ vars t
Stuck ⟨ _ , ((_ => _) ~ (_ => _)) :: _ ⟩ = ⊥

data _~>*_ : State -> State -> Set where
  refl : {S : State} -> S ~>* S
  step : {S S' S'' : State} -> S ~~> S' -> S' ~>* S'' -> S ~>* S''

lemma-measure : {S T : State} -> S ~> T -> measure T <² measure S
lemma-measure (nop {cs} {cs'} {i}) = make<² le lt
  where
    le = begin
           measure-l cs cs'                                    <=⟨ le-refl ⟩
           size (vars-rs cs ∪ vars-cs cs')                     <=⟨ le-size ⟩
           size (([ i ] ∪ [ i ]) ∪ (vars-rs cs ∪ vars-cs cs')) ==⟨ size-union-assoc ⟩
           size (vars-rs cs ∪ (([ i ] ∪ [ i ]) ∪ vars-cs cs')) <=⟨ le-refl ⟩
           measure-l cs ((var i ~ var i) :: cs')
         end
    lt = begin
           succ (measure-r cs')               <=⟨ <=-succ le-refl ⟩
           succ (succ (measure-r cs'))        <=⟨ le-refl ⟩
           measure-r ((var i ~ var i) :: cs')
         end
lemma-measure (sub i t i∉t) = {!!}
lemma-measure (arr {cs} {cs'} {t} {s} {u} {v}) = make<² le lt
  where
    le = begin
           measure-l cs ((t ~ u) :: (s ~ v) :: cs') <=⟨ le-refl ⟩
           size (vars-rs cs ∪ vars-cs ((t ~ u) :: (s ~ v) :: cs')) <=⟨ le-refl ⟩
           size (vars-rs cs ∪ ((vars t ∪ vars u) ∪ ((vars s ∪ vars v) ∪ vars-cs cs'))) <=⟨ {!!} ⟩
           measure-l cs (((t => s) ~ (u => v)) :: cs')
         end
    lt = {!!}

-- lemma-measure {n} (nop {_} {cs} {cs'} {i}) =
--   begin
--     succ (measure ⟨ cs , cs' ⟩) ==⟨ refl ⟩
--     succ (measure-l cs cs' + measure-r cs')
--       ==⟨ +-succ (measure-l cs cs') (measure-r cs') ⟩
--     measure-l cs cs' + succ (measure-r cs')
--       <=⟨ <=-cong-+ (lemma-measure-l-1 cs cs' i) (lemma-measure-r-1 cs' i) ⟩
--     measure-l cs ((var i ~ var i) :: cs') + measure-r ((var i ~ var i) :: cs')
--       ==⟨ refl ⟩
--     measure ⟨ cs , (var i ~ var i) :: cs' ⟩
--   end
-- lemma-measure (sub i t i∉t) = {!!}
-- lemma-measure arr = {!!}

lemma-measure' : {S T : State} -> S ~~> T -> measure T <² measure S
lemma-measure' (here red) = lemma-measure red
lemma-measure' (swap red) = {!!}

solver : (cs : Constraints) -> ∃[ S ] Stuck S ∧ ⟨ [] , cs ⟩ ~>* S
solver cs = aux ⟨ [] , cs ⟩ (well-founded-⊏ ⟨ [] , cs ⟩)
  where
    aux : (S : State) -> Accessible _⊏_ S -> ∃[ S' ] Stuck S' ∧ S ~>* S'
    aux ⟨ cs , [] ⟩ (acc f) = ⟨ cs , [] ⟩ , <> , refl
    aux ⟨ cs , ((var i ~ t@(var j)) :: cs') ⟩ (acc f) with i =? j
    ... | yes refl =
      let S , stuck , reds = aux ⟨ cs , cs' ⟩ (f _ (lemma-measure (nop {cs} {cs'}))) in
      S , stuck , step (here nop) reds
    ... | no neq =
      let S , stuck , reds = aux ⟨ (var i ~ t) :: subst-cs (i >-> t) cs
                                 , subst-cs (i >-> t) cs' ⟩
                                 (f _ (lemma-measure (sub {cs} {cs'} i t λ { refl -> neq refl} )))
      in S , stuck , step (here (sub i t λ { refl → neq refl})) reds
    aux ⟨ cs , (c@(var i ~ t@(_ => _)) :: cs') ⟩ (acc f) with i ∈? t
    ... | yes i∈t = ⟨ cs , c :: cs' ⟩ , i∈t , refl
    ... | no i∉t =
      let S , stuck , reds = aux ⟨ (var i ~ t) :: subst-cs (i >-> t) cs
                                 , subst-cs (i >-> t) cs' ⟩
                                 (f _ (lemma-measure (sub {cs} {cs'} i t i∉t)))
      in S , stuck , step (here (sub i t i∉t)) reds
    aux ⟨ cs , (c@(t@(_ => _) ~ var i) :: cs') ⟩ (acc f) with i ∈? t
    ... | yes i∈t = ⟨ cs , c :: cs' ⟩ , i∈t , refl
    ... | no i∉t =
      let S , stuck , reds = aux ⟨ (var i ~ t) :: subst-cs (i >-> t) cs
                                 , subst-cs (i >-> t) cs' ⟩
                                 (f _ (lemma-measure' (swap {cs} {cs'} (here (sub i t i∉t)))))
      in S , stuck , step (swap (here (sub i t i∉t))) reds
    aux ⟨ cs , (((t => s) ~ (u => v)) :: cs') ⟩ (acc f) =
      let S , stuck , reds = aux ⟨ cs , (t ~ u) :: (s ~ v) :: cs' ⟩
                                 (f _ (lemma-measure (arr {cs} {cs'} {t})))
      in S , stuck , step (here arr) reds

-- -- solver = aux [] <>
-- --   where
-- --     aux : {n : ℕ} (sub : Substitution n) -> Solution sub -> List (Constraint) -> Maybe (∃[ xs ] Solution xs)
-- --     aux sub sol [] = just (sub , sol)
-- --     aux sub sol ((var i ~ var j) :: xs) with i =? j
-- --     ... | yes i=j = aux sub sol xs
-- --     ... | no i!=j = {!!}
-- --     aux sub sol ((var i ~ t@(arr _ _)) :: xs) with i ∈? t
-- --     ... | yes i∈t = nothing
-- --     ... | no ¬i∈t = {!!}
-- --     aux sub sol ((t@(arr _ _) ~ var i) :: xs) with i ∈? t
-- --     ... | yes i∈t = nothing
-- --     ... | no ¬i∈t = {!!}
-- --     aux sub sol ((arr t s ~ arr u v) :: xs) = aux sub sol ((t ~ u) :: (s ~ v) :: xs)
