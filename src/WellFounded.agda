module WellFounded where

data Accessible {A : Set} (_<_ : A -> A -> Set) (x : A) : Set where
  acc : ((y : A) -> y < x -> Accessible _<_ y) -> Accessible _<_ x

WellFounded : {A : Set} -> (A -> A -> Set) -> Set
WellFounded {A} _<_ = (x : A) -> Accessible _<_ x

-- induction principle

-- weak-induction : {P : ℕ -> Set} -> P 0 -> ((x : ℕ) -> P x -> P (succ x)) -> (x : ℕ) -> P x
-- weak-induction p f zero = p
-- weak-induction p f (succ x) = f x (weak-induction p f x)

-- strong-induction : {P : ℕ -> Set} ->
--   ((x : ℕ) -> ((y : ℕ) -> y < x -> P y) -> P x) ->
--   (x : ℕ) -> P x
-- strong-induction f x = {!!}
