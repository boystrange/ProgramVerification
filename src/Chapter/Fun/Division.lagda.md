---
---

```agda
module Chapter.Fun.Division where

open import Library.Nat
open import Library.Nat.Properties
open import Library.List
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning
open import Library.LessThan
open import Library.LessThan.Reasoning renaming (begin_ to <=begin_; _end to _<=end) hiding (_==⟨_⟩_)
open import Library.WellFounded

+-minus-assoc : (x y z : ℕ) -> z <= y -> x + (y - z) == (x + y) - z
+-minus-assoc x y 0 le-zero =
  begin
    x + (y - 0) ==⟨ cong (x +_) (minus-zero y) ⟩
    x + y       ==⟨ symm (minus-zero (x + y)) ⟩
    (x + y) - 0
  end
+-minus-assoc x (succ y) (succ z) (le-succ le) =
  begin
    x + (succ y - succ z) ==⟨⟩
    x + (y - z)           ==⟨ +-minus-assoc x y z le ⟩
    (x + y) - z           ==⟨ refl ⟩
    succ (x + y) - succ z ==⟨ refl ⟩
    (succ x + y) - succ z ==⟨ cong (_- succ z) (+-succ x y) ⟩
    (x + succ y) - succ z
  end

{-# TERMINATING #-}
nt-division : (x y : ℕ) -> (0 < y) -> ∃[ q ] ∃[ r ] (r < y) ∧ (q * y + r == x)
nt-division x y 0<y with x <? y
... | inr lt = 0 , x , lt , refl
... | inl nlt with not-lt-ge nlt
... | ge with nt-division (x - y) y 0<y
... | q , r , r<y , qy=x = succ q , r , r<y , eq
  where
    eq : succ q * y + r == x
    eq = begin
           succ q * y + r  ==⟨⟩
           y + q * y + r   ==⟨ symm (+-assoc y (q * y) r) ⟩
           y + (q * y + r) ==⟨ cong (y +_) qy=x ⟩
           y + (x - y)     ==⟨ +-minus-assoc y x y ge ⟩
           (y + x) - y     ==⟨ +-minus y x ⟩
           x
         end
```

```agda
open import Library.LessThan.Alternative

accessible<' : (x y : ℕ) -> y <' x -> Accessible _<'_ y
accessible<' (succ y) _ le-refl'      = acc (accessible<' y)
accessible<' (succ y) z (le-succ' lt) = accessible<' y z lt

well-founded-lt' : WellFounded _<'_
well-founded-lt' x = acc (accessible<' x)

_<'?_ : (x y : ℕ) -> Decidable (x <' y)
x <'? y with x <? y
... | inr x<y = inr (<=to<=' x<y)
... | inl ¬x<y = inl λ x<y -> ¬x<y (<='to<= x<y)

minus-succ : {x y : ℕ} -> (y < x) -> (x - succ y < x - y)
minus-succ {succ x} {zero} p rewrite minus-zero x = le-refl
minus-succ {succ x} {succ y} (le-succ p) = minus-succ p

minus-le : (x y : ℕ) -> (x - y <= x)
minus-le zero     _        = le-zero
minus-le (succ _) zero     = le-refl
minus-le (succ x) (succ y) = le-succ-r (minus-le x y)

minus-lt : {x y : ℕ} -> (0 < y) -> (y <= x) -> (x - y < x)
minus-lt {x} {succ y} _ q =
  <=begin
    x - succ y <⟨ minus-succ q ⟩
    x - y      <=⟨ minus-le x y ⟩
    x
  <=end

minus-lt' : {x y : ℕ} -> (0 <' y) -> (y <=' x) -> (x - y <' x)
minus-lt' p q = <=to<=' (minus-lt (<='to<= p) (<='to<= q))

not-lt-ge' : {x y : ℕ} -> ¬ (x <' y) -> (y <=' x)
not-lt-ge' p = <=to<=' (not-lt-ge λ q -> p (<=to<=' q))

div-rem-aux : (x y : ℕ) -> 0 <' y -> Accessible _<'_ x -> ∃[ q ] ∃[ r ] r <' y ∧ q * y + r == x
div-rem-aux x y p (acc f) with x <'? y
... | inr lt = 0 , x , lt , refl
... | inl nlt with not-lt-ge' nlt
... | ge with div-rem-aux (x - y) y p (f (x - y) (minus-lt' p ge))
... | q , r , r<y , qy=x =
  succ q , r , r<y , (
    begin
      succ q * y + r  ==⟨⟩
      y + q * y + r   ==⟨ symm (+-assoc y (q * y) r) ⟩
      y + (q * y + r) ==⟨ cong (y +_) qy=x ⟩
      y + (x - y)     ==⟨ +-minus-assoc y x y (<='to<= ge) ⟩
      (y + x) - y     ==⟨ +-minus y x ⟩
      x
    end)

division : (x y : ℕ) -> (0 < y)-> ∃[ q ] ∃[ r ] (r < y) ∧ (q * y + r == x)
division x y 0<y with div-rem-aux x y (<=to<=' 0<y) (well-founded-lt' x)
... | q , r , r<y , qy=x = q , r , <='to<= r<y , qy=x
```
