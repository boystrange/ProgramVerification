---
title: Polymorphic functions and implicit arguments
next:  Chapter.Intro.Lists
prev:  Chapter.Intro.NaturalNumbers
---

```
module Chapter.Intro.Polymorphism where
```

In this chapter we study Agda's support for **polymorphism**, namely
the ability of some functions to be applied to arguments of
different types.

## Imports

```
open import Library.Bool
open import Library.Nat
```

## Polymorphic functions

The behavior of some functions does not depend on any particular
property of their argument. The simplest example of function with
such property is that of the **identity function**, which always
yields the value of its argument. We may conceive several versions
of the identity function, depending on the type of its argument.

```
id₁ : Bool -> Bool
id₁ x = x

id₂ : ℕ -> ℕ
id₂ x = x

id₃ : (ℕ -> Bool) -> (ℕ -> Bool)
id₃ x = x
```

Depending on the type of the argument, we would use one version or
the other: if we want to apply the identity function to a boolean
value, then we would use `id₁`; if we want to apply the identity
function to a natural number, then we would use `id₂`; and so on and
so forth.

```
_ : Bool
_ = id₁ true

_ : ℕ
_ = id₂ 42
```

The definitions `id₁`, `id₂`, ... of the identity function differ in
the type of their argument, but behave in exactly the same
way. Clearly, it would be desirable to define the identity function
once and for all, and make it applicable to arguments of different
types. In Agda this is made possible by the dependent arrow type.

```
id₄ : ∀(A : Set) -> A -> A
id₄ A x = x
```

Note that the domain of `id₄` is some `Set` `A` (that is, `A` is a
type in Agda's terminology) and the codomain of `id₄` is the type `A
-> A`. Basically, we have turned the one-argument, monomorphic
identity function into a two-arguments, polymorphic identity
function where the first argument is the type of the second
argument. We can now use `id₄` in different places with different
argument types.

```
_ : Bool
_ = id₄ Bool true

_ : ℕ
_ = id₄ ℕ 42
```

## Implicit arguments

You may have noticed that the argument `A` in the definition of
`id₄` plays no role in the definition of `id₄`. In fact, that
argument is somewhat *redundant* since it must coincide with the
type of `x`, the second argument of `id₄`. We can verify this
redundancy in practice by observing that Agda can automatically
*infer* the type of the first argument whenever we provide the
second one.

```
_ : Bool
_ = id₄ _ true

_ : ℕ
_ = id₄ _ 42
```

In these definitions, the underscore `_` stands for an expression
that we ask Agda to automatically infer. Of course, not everything
can be inferred automatically, or else there would be no point in
learning how to program in Agda. In the particular case of `id₄`,
however, the term that is meant to replace the underscore is
uniquely determined by the second argument: since `true` has type
`Bool`, the first underscore must be replaced by `Bool`; since `42`
has type `ℕ`, the second underscore must be replaced by `ℕ`. This
fact makes `id₄` slightly annoying to use, since the programmer is
required to systematically provide an argument that Agda can infer
by itself. In the end, the programmer will typically apply `id₄` to
an underscore followed by the actual argument. We can spare this
burden to the programmer by declaring that the first argument of
`id₄` is **implicit**. As the name suggests, implicit arguments can
be omitted in the program since they are supposed to be inferred
automatically. An implicit argument is declared using braces `{...}`
instead of parentheses `(...)`. So, the final version of the
polymorphic identity function with implicit arguments is the
following.

```
id : ∀{A : Set} -> A -> A
id x = x
```

Notice that the implicit argument is also omitted in the very
definition of `id`. Now, we can apply `id` to whatever argument we
like, without explicitly supplying its type.

```
_ : Bool
_ = id true

_ : ℕ
_ = id 42
```

There are cases in which Agda is not able to automatically infer an
implicit. In these cases, we can supply it explicitly, by placing
the implicit argument within braces.

```
_ : Bool
_ = id {Bool} true

_ : ℕ
_ = id {ℕ} 42
```

Similarly, we can name the implicit argument when defining the
function, in case it is needed in the body of the function.

```
id₅ : ∀{A : Set} -> A -> A
id₅ {A} x = x
```

There is no general guideline to establish whether an argument
should be explicit or implicit. As a rule of thumb, an argument can
be declared implicit if it also occurs later in the same type. We
will see systematic applications of this rule in the next chapters,
as we make greater use of dependent types.

## Exercises

1. Implement the function `flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C`.
2. Implement the function `_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C`.
3. Provide two syntactically different (but equivalent)
   implementations of the function `apply : ∀{A B : Set} -> (A -> B) -> A -> B`.

```agda
flip : ∀{A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip = λ f x y -> f y x

_∘_ : ∀{A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)

-- the first version of apply follows from the definition of
-- function application

apply₁ : ∀{A B : Set} -> (A -> B) -> A -> B
apply₁ f x = f x

-- the second version of apply is just a specialized identity
-- function

apply₂ : ∀{A B : Set} -> (A -> B) -> A -> B
apply₂ x = x
```
{:.solution}
