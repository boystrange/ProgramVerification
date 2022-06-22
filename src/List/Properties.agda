module List.Properties where

open import Fun
open import Nat
open import List
open import Equality
open import Equality.Reasoning
open import Logic

::-injective : ∀{A : Set} {x y : A} {xs ys : List A} -> x :: xs == y :: ys -> x == y ∧ xs == ys
::-injective refl = refl , refl

++-length : ∀{A : Set} (xs ys : List A) -> length (xs ++ ys) == length xs + length ys
++-length []        ys = refl
++-length (_ :: xs) ys = cong succ (++-length xs ys)

++-assoc : ∀{A : Set} (xs ys zs : List A) -> xs ++ (ys ++ zs) == (xs ++ ys) ++ zs
++-assoc [] ys zs = refl
++-assoc (x :: xs) ys zs = cong (x ::_) (++-assoc xs ys zs)

lemma-++-[] : ∀{A : Set} (xs : List A) -> xs ++ [] == xs
lemma-++-[] [] = refl
lemma-++-[] (x :: xs) = cong (x ::_) (lemma-++-[] xs)

lemma-[]-++ : ∀{A : Set} (xs ys : List A) -> [] == xs ++ ys -> xs == [] ∧ ys == []
lemma-[]-++ [] _ refl = refl , refl

reverse-++ : ∀{A : Set} (xs ys : List A) -> reverse (xs ++ ys) == reverse ys ++ reverse xs
reverse-++ [] ys = symm (lemma-++-[] (reverse ys))
reverse-++ (x :: xs) ys =
  begin
    reverse ((x :: xs) ++ ys)           ==⟨⟩
    reverse (x :: (xs ++ ys))           ==⟨⟩
    reverse (xs ++ ys) ++ [ x ]         ==⟨ cong (_++ [ x ]) (reverse-++ xs ys) ⟩
    (reverse ys ++ reverse xs) ++ [ x ] ==⟨ symm (++-assoc (reverse ys) (reverse xs) [ x ]) ⟩
    reverse ys ++ (reverse xs ++ [ x ]) ==⟨⟩
    (reverse ys ++ reverse (x :: xs))
  end

reverse-involution : ∀{A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-involution [] = refl
reverse-involution (x :: xs) =
  begin
    reverse (reverse (x :: xs))           ==⟨⟩
    reverse (reverse xs ++ [ x ])         ==⟨ reverse-++ (reverse xs) [ x ] ⟩
    reverse [ x ] ++ reverse (reverse xs) ==⟨⟩
    x :: reverse (reverse xs)             ==⟨ cong (x ::_) (reverse-involution xs) ⟩
    (x :: xs)
  end

lemma-reverse-onto : ∀{A : Set} (xs ys : List A) -> reverse-onto xs ys == reverse xs ++ ys
lemma-reverse-onto [] ys = refl
lemma-reverse-onto (x :: xs) ys =
  begin
    reverse-onto (x :: xs) ys   ==⟨⟩
    reverse-onto xs (x :: ys)   ==⟨ lemma-reverse-onto xs (x :: ys) ⟩
    reverse xs ++ (x :: ys)     ==⟨⟩
    reverse xs ++ ([ x ] ++ ys) ==⟨ ++-assoc (reverse xs) [ x ] ys ⟩
    (reverse xs ++ [ x ]) ++ ys ==⟨⟩
    (reverse (x :: xs) ++ ys)
  end

fast-reverse-correct : ∀{A : Set} (xs : List A) -> fast-reverse xs == reverse xs
fast-reverse-correct xs =
  begin
    fast-reverse xs    ==⟨⟩
    reverse-onto xs [] ==⟨ lemma-reverse-onto xs [] ⟩
    reverse xs ++ []   ==⟨ lemma-++-[] (reverse xs) ⟩
    reverse xs
  end

map-compose : ∀{A B C : Set} (f : B -> C) (g : A -> B) (xs : List A) -> map f (map g xs) == map (f ∘ g) xs
map-compose f g [] = refl
map-compose f g (x :: xs) =
  begin
    map f (map g (x :: xs))       ==⟨⟩
    map f (g x :: map g xs)       ==⟨⟩
    f (g x) :: map f (map g xs)   ==⟨⟩
    (f ∘ g) x :: map f (map g xs) ==⟨ cong ((f ∘ g) x ::_) (map-compose f g xs) ⟩
    (f ∘ g) x :: map (f ∘ g) xs   ==⟨⟩
    map (f ∘ g) (x :: xs)
  end

all-++ : ∀{A : Set} {xs ys : List A} (P : A -> Set) -> all P xs -> all P ys -> all P (xs ++ ys)
all-++ {xs = []} P ps qs = qs
all-++ {xs = x :: xs} P (px , ps) qs = px , all-++ P ps qs

all-all : ∀{A : Set} {xs : List A} (P Q : A -> Set) -> (∀{x : A} -> P x -> Q x) -> all P xs -> all Q xs
all-all {xs = []} P Q imp ps = <>
all-all {xs = x :: xs} P Q imp (px , ps) = imp px , all-all P Q imp ps
