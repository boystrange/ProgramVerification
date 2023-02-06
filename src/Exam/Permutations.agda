module Exam.Permutations where

open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.List.Permutation
open import Library.Equality
open import Library.Equality.Reasoning

sum : List ℕ -> ℕ
sum [] = 0
sum (x :: xs) = x + sum xs

mul : List ℕ -> ℕ
mul [] = 1
mul (x :: xs) = x * mul xs

sum-permutation : {xs ys : List ℕ} -> xs # ys -> sum xs == sum ys
sum-permutation #refl = refl
sum-permutation (#swap {x} {y} {xs}) =
  begin
    x + (y + sum xs) ==⟨ +-assoc x y (sum xs) ⟩
    (x + y) + sum xs ==⟨ cong (_+ sum xs) (+-comm x y) ⟩
    (y + x) + sum xs ==⟨ symm (+-assoc y x (sum xs)) ⟩
    y + (x + sum xs)
  end
sum-permutation (#cong π) = cong (_ +_) (sum-permutation π)
sum-permutation (#trans π π') = tran (sum-permutation π) (sum-permutation π')

mul-permutation : {xs ys : List ℕ} -> xs # ys -> mul xs == mul ys
mul-permutation #refl = refl
mul-permutation (#swap {x} {y} {xs}) =
  begin
    mul (x :: y :: xs) ==⟨ refl ⟩
    x * mul (y :: xs)  ==⟨ refl ⟩
    x * (y * mul xs)   ==⟨ *-assoc x y (mul xs) ⟩
    (x * y) * mul xs   ==⟨ cong (_* mul xs) (*-comm x y) ⟩
    (y * x) * mul xs   ==⟨ symm (*-assoc y x (mul xs)) ⟩
    y * (x * mul xs)   ==⟨ refl ⟩
    y * mul (x :: xs)  ==⟨ refl ⟩
    mul (y :: x :: xs)
  end
mul-permutation (#cong {x} π) = cong (x *_) (mul-permutation π)
mul-permutation (#trans π π') = tran (mul-permutation π) (mul-permutation π')

length-permutation : {A : Set} {xs ys : List A} -> xs # ys -> length xs == length ys
length-permutation #refl = refl
length-permutation #swap = refl
length-permutation (#cong π) = cong succ (length-permutation π)
length-permutation (#trans π π') = tran (length-permutation π) (length-permutation π')

data Has {A : Set} : A -> List A -> Set where
  has-here : {x : A} {xs : List A} -> Has x (x :: xs)
  has-next : {x y : A} {xs : List A} -> Has x xs -> Has x (y :: xs)

has-permutation : {A : Set} {xs ys : List A} {x : A} -> xs # ys -> Has x xs -> Has x ys
has-permutation #refl p = p
has-permutation #swap has-here = has-next has-here
has-permutation #swap (has-next has-here) = has-here
has-permutation #swap (has-next (has-next p)) = has-next (has-next p)
has-permutation (#cong π) has-here = has-here
has-permutation (#cong π) (has-next p) = has-next (has-permutation π p)
has-permutation (#trans π π') p = has-permutation π' (has-permutation π p)

data Same {A : Set} (x : A) : List A -> Set where
  same-[] : Same x []
  same-:: : {xs : List A} -> Same x xs -> Same x (x :: xs)

lem : {A : Set} {x : A} {xs ys : List A} -> Same x xs -> xs # ys -> Same x ys
lem p #refl = p
lem (same-:: (same-:: p)) #swap = same-:: (same-:: p)
lem (same-:: p) (#cong π) = same-:: (lem p π)
lem p (#trans π π') = lem (lem p π) π'

thm : {A : Set} {x : A} {xs ys : List A} -> Same x xs -> xs # ys -> xs == ys
thm p #refl = refl
thm (same-:: (same-:: p)) #swap = refl
thm (same-:: p) (#cong π) = cong (_ ::_) (thm p π)
thm p (#trans π π') = tran (thm p π) (thm (lem p π) π')

-- same-++ : {A : Set} {x : A} {xs ys : List A} -> Same x xs -> Same x ys -> xs ++ ys == ys ++ xs
-- same-++ same-[] same-[] = refl
-- same-++ same-[] (same-:: q) = {!!}
-- same-++ (same-:: p) q = {!!}

same-cons : {A : Set} {x : A} {xs : List A} -> Same x xs -> x :: xs == xs ++ [ x ]
same-cons same-[] = refl
same-cons (same-:: p) = cong (_ ::_) (same-cons p)

same-reverse : {A : Set} {x : A} {xs : List A} -> Same x xs -> xs == reverse xs
same-reverse same-[] = refl
same-reverse {_} {x} {.x :: xs} (same-:: p) =
  begin
    x :: xs ==⟨ same-cons p ⟩
    xs ++ [ x ] ==⟨ cong (_++ [ x ]) (same-reverse p) ⟩
    reverse xs ++ [ x ] ==⟨ refl ⟩
    reverse (x :: xs)
  end

same-sum : {x : ℕ} {xs : List ℕ} -> Same x xs -> sum xs == length xs * x
same-sum same-[] = refl
same-sum {x} (same-:: p) = cong (x +_) (same-sum p)
