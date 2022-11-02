
open import Library.Bool
open import Library.Nat
open import Library.Nat.Properties
open import Library.Equality
open import Library.Equality.Reasoning

-- define two functions to establish whether a natural number is
-- even or odd, respectively. make sure that each function is
-- defined recursively by case analysis on its argument. In
-- particular, do *not* define odd as the negation of even nor even
-- as the negation of odd

even : ℕ -> Bool
even zero = true
even (succ zero) = false
even (succ (succ x)) = even x

odd : ℕ -> Bool
odd zero = false
odd (succ zero) = true
odd (succ (succ x)) = odd x

-- prove the theorem even-not-odd

even-not-odd : ∀(x : ℕ) -> even x == not (odd x)
even-not-odd zero = refl
even-not-odd (succ zero) = refl
even-not-odd (succ (succ x)) = even-not-odd x

-- prove the theorem not-even-odd without using recursion/induction

not-inv : ∀(x : Bool) -> not (not x) == x
not-inv true = refl
not-inv false = refl

not-even-odd : ∀(x : ℕ) -> not (even x) == odd x
not-even-odd x =
  begin
    not (even x)      ==⟨ cong not (even-not-odd x) ⟩
    not (not (odd x)) ==⟨ not-inv (odd x) ⟩
    odd x
  end

-- prove that x + x is always even

twice-even : ∀(x : ℕ) -> even (x + x) == true
twice-even zero = refl
twice-even (succ zero) = refl
twice-even (succ (succ x)) =
  begin
    even (succ (succ x) + succ (succ x))   ==⟨ refl ⟩
    even (succ (succ (x + succ (succ x)))) ==⟨ refl ⟩
    even (x + succ (succ x))               ==⟨ cong even (symm (+-succ x (succ x))) ⟩
    even (succ x + succ x)                 ==⟨ twice-even (succ x) ⟩
    true
  end

-- prove that 2 * x is always even without using case analysis

two-times-even : ∀(x : ℕ) -> even (2 * x) == true
two-times-even x =
  begin
    even (2 * x)       ==⟨ refl ⟩
    even (x + (x + 0)) ==⟨ cong even (cong (x +_) (+-unit-r x)) ⟩
    even (x + x)       ==⟨ twice-even x ⟩
    true
  end

-- define a function sum : ℕ -> ℕ such that sum n is the sum of the
-- first n natural numbers. check that the function works correctly
-- using C-c C-n

sum : ℕ -> ℕ
sum zero = zero
sum (succ x) = succ x + sum x

-- prove that the Gauss formula is correct

gauss : ∀(x : ℕ) -> 2 * sum x == x * succ x
gauss zero = refl
gauss (succ x) =
  begin
    2 * sum (succ x)                   ==⟨ refl ⟩
    2 * (succ x + sum x)               ==⟨ *-dist-l 2 (succ x) (sum x) ⟩
    2 * succ x + 2 * sum x             ==⟨ cong (2 * succ x +_) (gauss x) ⟩
    2 * succ x + x * succ x            ==⟨ refl ⟩
    succ x + (succ x + 0) + x * succ x ==⟨ cong (_+ x * succ x) (cong (succ x +_) (cong succ (+-unit-r x))) ⟩
    succ x + succ x + x * succ x       ==⟨ symm (+-assoc (succ x) (succ x) (x * succ x)) ⟩
    succ x + (succ x + x * succ x)     ==⟨ refl ⟩
    succ x + succ x * succ x           ==⟨ refl ⟩
    succ (succ x) * succ x             ==⟨ *-comm (succ (succ x)) (succ x) ⟩
    succ x * succ (succ x)
  end
