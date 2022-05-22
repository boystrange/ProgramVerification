
data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

first : ∀{A B : Set} -> A × B -> A
first (x , _) = x

second : ∀{A B : Set} -> A × B -> B
second (_ , y) = y
