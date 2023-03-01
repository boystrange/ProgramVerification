module Exam.Reminder where

open import Library.Nat
open import Library.Nat.Properties
open import Library.LessThan
open import Library.Logic
open import Library.Equality
open import Library.Equality.Reasoning

rem : (x : ℕ) -> ∃[ q ] ∃[ r ] r <= 1 ∧ x == q + q + r
rem zero        = 0 , 0 , le-zero , refl
rem (succ zero) = 0 , 1 , le-succ le-zero , refl
rem (succ (succ x)) with rem x
... | q , r , le , eq = succ q , r , le ,
  (begin
    succ (succ x) ==⟨ cong succ (cong succ eq) ⟩
    succ (succ (q + q + r)) ==⟨ refl ⟩
    succ (succ (q + q)) + r ==⟨ cong succ (cong (_+ r) (+-succ q q)) ⟩
    succ (q + succ q) + r ==⟨ refl ⟩
    succ q + succ q + r
  end)
