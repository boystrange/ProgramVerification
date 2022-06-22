module Fun where

-- CHECK IF NEEDED

id : {A : Set} -> A -> A
id x = x

const : {A B : Set} -> A -> B -> A
const x _ = x

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
_∘_ f g x = f (g x)

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f x y = f y x

-- CHECK IF NEEDED

-- curry : {A B C : Set} -> (A × B -> C) -> A -> B -> C
-- curry f x y = f (x , y)

-- uncurry : {A B C : Set} -> (A -> B -> C) -> A × B -> C
-- uncurry f (x , y) = f x y
