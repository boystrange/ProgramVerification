---
---

```agda
module Permutation where

open import List

-- exchange
data _#_ {A : Set} : List A -> List A -> Set where

-- permutation = finite sequence of exchanges
data _##_ {A : Set} : List A -> List A -> Set where
  none : ∀{xs : List A} -> xs ## xs
  here : ∀{x y : A} {xs : List A} -> (x :: (y :: xs)) ## (y :: (x :: xs))
  next : ∀{x : A} {xs ys : List A} -> xs ## ys -> (x :: xs) ## (x :: ys)
  _|>_ : ∀{xs ys zs : List A} -> xs ## ys -> ys ## zs -> xs ## zs

-- #-commutative : ∀{A : Set} {xs ys : List A} -> xs # ys -> ys # xs
-- #-commutative here = here
-- #-commutative (next p) = next (#-commutative p)

#begin_ : ∀{A : Set} {xs ys : List A} -> xs ## ys -> xs ## ys
#begin_ ps = ps

_#end : ∀{A : Set} (xs : List A) -> xs ## xs
_#end xs = none

_##⟨_⟩_ : ∀{A : Set} (xs : List A) {ys zs : List A} -> xs ## ys -> ys ## zs -> xs ## zs
_##⟨_⟩_ _ = _|>_

_##⟨⟩_ : ∀{A : Set} (xs : List A) {ys : List A} -> xs ## ys -> xs ## ys
_ ##⟨⟩ ps = ps

infix  1 #begin_
infixr 2 _##⟨⟩_ _##⟨_⟩_
infix  3 _#end

##-commutative : ∀{A : Set} {xs ys : List A} -> xs ## ys -> ys ## xs
##-commutative none = none
##-commutative here = here
##-commutative (next ps) = next (##-commutative ps)
##-commutative (ps |> qs) = ##-commutative qs |> ##-commutative ps

##-cong-l : ∀{A : Set} {xs ys zs : List A} -> xs ## ys -> (zs ++ xs) ## (zs ++ ys)
##-cong-l {zs = []} ps = ps
##-cong-l {zs = x :: zs} ps = next (##-cong-l ps)

##-cong-r : ∀{A : Set} {xs ys zs : List A} -> xs ## ys -> (xs ++ zs) ## (ys ++ zs)
##-cong-r none = none
##-cong-r here = here
##-cong-r (next ps) = next (##-cong-r ps)
##-cong-r (ps |> qs) = ##-cong-r ps |> ##-cong-r qs

##-push : ∀{A : Set} {x : A} {xs ys : List A} -> (x :: (xs ++ ys)) ## (xs ++ (x :: ys))
##-push {xs = []} = none
##-push {xs = x :: xs} =
  #begin
    _ ##⟨ here ⟩
    _ ##⟨ next ##-push ⟩
    _
  #end
```
