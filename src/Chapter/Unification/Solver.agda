module Chapter.Unification.Solver where

open import Unit
open import Nat hiding (_-_)
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
  _∈?_   : (i : Var) (t : Term) -> Decidable (i ∈ vars t)
  size   : Domain -> ℕ
  ⊊-size : {X Y : Domain} -> X ⊊ Y -> size X < size Y
  ⊆-size : {X Y : Domain} -> X ⊆ Y -> size X <= size Y

=-size : {X Y : Domain} -> X ⊆ Y -> Y ⊆ X -> size X == size Y
=-size inc1 inc2 = le-antisymm (⊆-size inc1) (⊆-size inc2)

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
accessible<²' (.(succ _) , _) q        (left refl)              = acc (accessible<²' q)
accessible<²' (succ x , y)    q        (left (succ lt))         = accessible<²' (x , y) q (left lt)
accessible<²' (x , succ y)    (.x , u) (right (refl , refl))    = acc (accessible<²' (x , u))
accessible<²' (x , succ y)    (.x , u) (right (refl , succ lt)) = accessible<²' (x , y) (x , u) (right (refl , lt))

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

make<=² : {x y u v : ℕ} -> x <= u -> y <= v -> (x , y) <=² (u , v)
make<=² {x} {y} {u} {v} le1 le2 with x =? u
... | yes refl = right (refl , le2)
... | no neq = left (le-ne-lt le1 neq)

<=²-trans : {p q r : Measure} -> p <=² q -> q <=² r -> p <=² r
<=²-trans (left lt1) (left lt2) = left (le-trans (<=-succ lt1) lt2)
<=²-trans (left lt) (right (refl , le)) = left lt
<=²-trans (right (refl , le)) (left lt) = left lt
<=²-trans (right (refl , le1)) (right (refl , le2)) = make<=² le-refl (le-trans le1 le2)

make<²l : {x y u v : ℕ} -> x < u -> (x , y) <² (u , v)
make<²l = left

make<²r : {x y u v : ℕ} -> x == u -> y < v -> (x , y) <² (u , v)
make<²r eq lt = right (eq , lt)

make<² : {x y u v : ℕ} -> x <= u -> y < v -> (x , y) <² (u , v)
make<² {x} {_} {u} le lt with x =? u
... | yes eq = right (eq , lt)
... | no neq = left (le-ne-lt le neq)

Stuck : State -> Set
Stuck ⟨ _ , [] ⟩ = ⊤
Stuck ⟨ _ , (var i ~ var _) :: _ ⟩ = ⊥
Stuck ⟨ _ , (var i ~ t@(_ => _)) :: _ ⟩ = i ∈ vars t
Stuck ⟨ _ , (t@(_ => _) ~ var i) :: _ ⟩ = i ∈ vars t
Stuck ⟨ _ , ((_ => _) ~ (_ => _)) :: _ ⟩ = ⊥

data _~>*_ : State -> State -> Set where
  refl : {S : State} -> S ~>* S
  step : {S S' S'' : State} -> S ~~> S' -> S' ~>* S'' -> S ~>* S''

lemma-apply : (i : Var) (t s : Term) -> vars (apply (i >-> t) s) ⊆ (vars t ∪ (vars s - [ i ]))
lemma-apply i t (var j) {k} K with i =? j
... | yes refl = left K
lemma-apply i t (var j) {.j} refl | no neq = right (refl , neq)
lemma-apply i t (s1 => s2) {k} (left K) with lemma-apply i t s1 K
... | left K' = left K'
... | right (K' , neq) = right (left K' , neq)
lemma-apply i t (s1 => s2) {k} (right K) with lemma-apply i t s2 K
... | left K' = left K'
... | right (K' , neq) = right (right K' , neq)

lemma-apply-c : (i : Var) (t : Term) (c : Constraint) ->
  vars-c (subst-c (i >-> t) c) ⊆ (vars t ∪ (vars-c c - [ i ]))
lemma-apply-c i t (s1 ~ s2) {k} (left K) with lemma-apply i t s1 K
... | left x = left x
... | right (x , neq) = right (left x , neq)
lemma-apply-c i t (s1 ~ s2) {k} (right x) with lemma-apply i t s2 x
... | left x = left x
... | right (x , neq) = right (right x , neq)

lemma-apply-r : (i : Var) (t : Term) (c : Constraint) ->
  vars-r (subst-c (i >-> t) c) ⊆ (vars t ∪ (vars-r c - [ i ]))
lemma-apply-r i t (_ ~ s) x = lemma-apply i t s x

lemma-apply-cs : (i : Var) (t : Term) (cs : Constraints) ->
  vars-cs (subst-cs (i >-> t) cs) ⊆ (vars t ∪ (vars-cs cs - [ i ]))
lemma-apply-cs i t (c :: cs) (left x) with lemma-apply-c i t c x
... | left x = left x
... | right (x , neq) = right (left x , neq)
lemma-apply-cs i t (c :: cs) (right x) with lemma-apply-cs i t cs x
... | left x = left x
... | right (x , neq) = right (right x , neq)

lemma-apply-rs : (i : Var) (t : Term) (cs : Constraints) ->
  vars-rs (subst-cs (i >-> t) cs) ⊆ (vars t ∪ (vars-rs cs - [ i ]))
lemma-apply-rs i t (c :: cs) (left x) with lemma-apply-r i t c x
... | left x = left x
... | right (x , neq) = right (left x , neq)
lemma-apply-rs i t (c :: cs) (right x) with lemma-apply-rs i t cs x
... | left x = left x
... | right (x , neq) = right (right x , neq)

lemma-measure : {S T : State} -> S ~> T -> measure T <² measure S
lemma-measure (nop {cs} {cs'} {i}) = make<² le lt
  where
    &cs = vars-rs cs
    &cs' = vars-cs cs'
    &i   = [ i ]

    lem1 : (A B C D : Domain) -> ((A ∪ B) ∪ (C ∪ D)) ⊆ (C ∪ ((A ∪ B) ∪ D))
    lem1 A B C D (left (left x)) = right (left (left x))
    lem1 A B C D (left (right x)) = right (left (right x))
    lem1 A B C D (right (left x)) = left x
    lem1 A B C D (right (right x)) = right (right x)

    lem2 : (A B : Domain) -> A ⊆ (B ∪ A)
    lem2 A B = right

    le = begin
           measure-l cs cs'                      <=⟨ le-refl ⟩
           size (&cs ∪ &cs')                     <=⟨ ⊆-size (lem2 (&cs ∪ &cs') (&i ∪ &i)) ⟩
           size ((&i ∪ &i) ∪ (&cs ∪ &cs'))       <=⟨ ⊆-size (lem1 &i &i &cs &cs') ⟩
           size (&cs ∪ ((&i ∪ &i) ∪ &cs'))       <=⟨ le-refl ⟩
           measure-l cs ((var i ~ var i) :: cs')
         end

    lt = begin
           succ (measure-r cs')               <=⟨ <=-succ le-refl ⟩
           succ (succ (measure-r cs'))        <=⟨ le-refl ⟩
           measure-r ((var i ~ var i) :: cs')
         end
lemma-measure (sub {cs} {cs'} i t i∉t) = make<²l lt
  where
    &t = vars t
    &tcs = vars-rs (subst-cs (i >-> t) cs)
    &tcs' = vars-cs (subst-cs (i >-> t) cs')
    &i = [ i ]
    &cs = vars-rs cs
    &cs' = vars-cs cs'
    &csi = &cs - &i
    &cs'i = &cs' - &i

    le1 : &tcs ⊆ (&t ∪ &csi) -> &tcs' ⊆ (&t ∪ &cs'i) -> ((&t ∪ &tcs) ∪ &tcs') ⊆ ((&t ∪ &csi) ∪ &cs'i)
    le1 inc1 inc2 {i} (left (left x)) = left (left x)
    le1 inc1 inc2 {i} (left (right x)) = left (inc1 x)
    le1 inc1 inc2 {i} (right x) with inc2 x
    ... | left x = left (left x)
    ... | right x = right x

    le2 : (A : Domain) (i : Var) -> i ∉ A -> size A < size ([ i ] ∪ A)
    le2 A i inot = ⊊-size (right , i , left refl , inot)

    le3 : (&i ∪ ((&t ∪ &csi) ∪ &cs'i)) ⊆ (&cs ∪ ((&i ∪ &t) ∪ &cs'))
    le3 {j} (left x) = right (left (left x))
    le3 {j} (right (left (left x))) = right (left (right x))
    le3 {j} (right (left (right (x , _)))) = left x
    le3 {j} (right (right (x , _))) = right (right x)

    inot : i ∉ ((&t ∪ &csi) ∪ &cs'i)
    inot (left (left x)) = i∉t x
    inot (left (right (_ , x))) = absurd (x refl)
    inot (right (_ , x)) = absurd (x refl)

    lt = begin
           succ (size ((&t ∪ &tcs) ∪ &tcs'))
             <=⟨ succ (⊆-size (le1 (lemma-apply-rs i t cs) (lemma-apply-cs i t cs'))) ⟩
           succ (size ((&t ∪ &csi) ∪ &cs'i)) <=⟨ le2 (((&t ∪ &csi) ∪ &cs'i)) i inot ⟩
           size (&i ∪ ((&t ∪ &csi) ∪ &cs'i)) <=⟨ ⊆-size le3 ⟩
           size (&cs ∪ ((&i ∪ &t) ∪ &cs'))
         end
lemma-measure (arr {cs} {cs'} {t} {s} {u} {v}) = make<² le lt
  where
    CS = vars-rs cs
    T = vars t
    U = vars u
    S = vars s
    V = vars v
    CS' = vars-cs cs'

    lem1 : (CS ∪ ((T ∪ U) ∪ ((S ∪ V) ∪ CS'))) ⊆ (CS ∪ (((T ∪ S) ∪ (U ∪ V)) ∪ CS'))
    lem1 (left a) = left a
    lem1 (right (left (left b))) = right (left (left (left b)))
    lem1 (right (left (right c))) = right (left (right (left c)))
    lem1 (right (right (left (left d)))) = right (left (left (right d)))
    lem1 (right (right (left (right e)))) = right (left (right (right e)))
    lem1 (right (right (right f))) = right (right f)

    le = begin
           measure-l cs ((t ~ u) :: (s ~ v) :: cs')        <=⟨ le-refl ⟩
           size (CS ∪ vars-cs ((t ~ u) :: (s ~ v) :: cs')) <=⟨ le-refl ⟩
           size (CS ∪ ((T ∪ U) ∪ ((S ∪ V) ∪ CS')))         <=⟨ ⊆-size lem1 ⟩
           size (CS ∪ (((T ∪ S) ∪ (U ∪ V)) ∪ CS'))         <=⟨ le-refl ⟩
           measure-l cs (((t => s) ~ (u => v)) :: cs')
         end

    #t = size-t t
    #s = size-t s
    #u = size-t u
    #v = size-t v
    #cs' = size-cs cs'
    #ts = size-t (t => s)
    #uv = size-t (u => v)

    lt = begin
           succ (measure-r ((t ~ u) :: (s ~ v) :: cs')) <=⟨ le-refl ⟩
           succ (#t + #u + (#s + #v + #cs'))            ==⟨ cong succ (very-stupid-lemma #t #u #s #v #cs') ⟩
           succ (#t + #s + (#u + #v + #cs'))            <=⟨ <=-succ le-refl ⟩
           succ (succ (#t + #s) + (#u + #v + #cs'))     <=⟨ le-refl ⟩
           succ (#ts + (#u + #v + #cs'))                ==⟨ +-succ #ts _ ⟩
           #ts + succ (#u + #v + #cs')                  <=⟨ le-refl ⟩
           #ts + (#uv + #cs')                           ==⟨ (+-associative #ts _ _) ⟩
           (#ts + #uv) + #cs'                           <=⟨ le-refl ⟩
           size-cs (((t => s) ~ (u => v)) :: cs')       ==⟨ refl ⟩
           measure-r (((t => s) ~ (u => v)) :: cs')
         end

lemma-measure' : {S T : State} -> S ~~> T -> measure T <² measure S
lemma-measure' (here red) = lemma-measure red
lemma-measure' (swap {cs} {cs'} {t} {s} red) =
  let lt = lemma-measure' red in
  <=²-trans lt (make<=² le1 le2)
  where
    lem1 : (A B C D : Domain) -> (A ∪ ((B ∪ C) ∪ D)) ⊆ (A ∪ ((C ∪ B) ∪ D))
    lem1 A B C D (left a) = left a
    lem1 A B C D (right (left (left b))) = right (left (right b))
    lem1 A B C D (right (left (right c))) = right (left (left c))
    lem1 A B C D (right (right d)) = right (right d)

    le1 = begin
            size (vars-rs cs ∪ ((vars s ∪ vars t) ∪ vars-cs cs'))
              <=⟨ ⊆-size (lem1 (vars-rs cs) (vars s) (vars t) (vars-cs cs')) ⟩
            size (vars-rs cs ∪ ((vars t ∪ vars s) ∪ vars-cs cs'))
          end

    le2 = begin
            size-t s + size-t t + size-cs cs'
              ==⟨ cong (_+ size-cs cs') (+-commutative (size-t s) (size-t t)) ⟩
            size-t t + size-t s + size-cs cs'
          end

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
