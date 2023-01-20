module Exam.Sublist where

open import Library.List
open import Library.Nat
open import Library.LessThan
open import Library.Equality
open import Library.Logic
open import Library.Logic.Laws

-- define the bredicate Sublist xs ys that holds whenever xs is a
-- sublist of ys, namely when all the elements of xs occur (in the
-- same order) also in ys

data Sublist {A : Set} : List A -> List A -> Set where
  sl-done : {ys : List A} -> Sublist [] ys
  sl-here : {x : A} {xs ys : List A} -> Sublist xs ys -> Sublist (x :: xs) (x :: ys)
  sl-next : {y : A} {xs ys : List A} -> Sublist xs ys -> Sublist xs (y :: ys)

-- prove that Sublist xs ys -> length xs <= length ys

sublist-length : {A : Set} {xs ys : List A} -> Sublist xs ys -> length xs <= length ys
sublist-length sl-done = le-zero
sublist-length (sl-here p) = le-succ (sublist-length p)
sublist-length (sl-next p) = le-succ-r (sublist-length p)

sublist-refl : {A : Set} (xs : List A) -> Sublist xs xs
sublist-refl [] = sl-done
sublist-refl (x :: xs) = sl-here (sublist-refl xs)

sublist-:: : {A : Set} {x : A} {xs ys : List A} -> Sublist (x :: xs) ys -> Sublist xs ys
sublist-:: (sl-here p) = sl-next p
sublist-:: (sl-next p) = sl-next (sublist-:: p)

sublist-trans : {A : Set} {xs ys zs : List A} ->
                Sublist xs ys -> Sublist ys zs -> Sublist xs zs
sublist-trans sl-done q = sl-done
sublist-trans (sl-here p) (sl-here q) = sl-here (sublist-trans p q)
sublist-trans (sl-here p) (sl-next q) = sl-next (sublist-trans (sl-here p) q)
sublist-trans (sl-next p) (sl-here q) = sl-next (sublist-trans p q)
sublist-trans {_} {xs} {y :: ys} {z :: zs} (sl-next p) (sl-next q) =
  sl-next (sublist-trans p (sublist-:: q))

sublist-absurd : {A : Set} {x y : A} {xs ys : List A} -> Sublist (x :: xs) ys ->
                 Sublist (y :: ys) xs -> ⊥
sublist-absurd (sl-here p) (sl-here q) = sublist-absurd p q
sublist-absurd (sl-here p) (sl-next q) = sublist-absurd p (sublist-:: q)
sublist-absurd (sl-next p) (sl-here q) = sublist-absurd (sublist-:: p) q
sublist-absurd (sl-next p) (sl-next q) = sublist-absurd (sublist-:: p) (sublist-:: q)

sublist-antisymm : {A : Set} {xs ys : List A} -> Sublist xs ys ->
                   Sublist ys xs -> xs == ys
sublist-antisymm sl-done sl-done = refl
sublist-antisymm (sl-here p) (sl-here q) = cong (_ ::_) (sublist-antisymm p q)
sublist-antisymm (sl-here p) (sl-next q) = cong (_ ::_) (sublist-antisymm p (sublist-:: q))
sublist-antisymm (sl-next p) (sl-here q) = cong (_ ::_) (sublist-antisymm (sublist-:: p) q)
sublist-antisymm {_} {x :: xs} {y :: ys} (sl-next p) (sl-next q) = ex-falso (sublist-absurd p q)
