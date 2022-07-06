---
title: "Inductive data types: the Booleans"
---

<!--
```
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.Bool where
```
-->

In this chapter we start looking at the constructs for defining and
using new data types in Agda.

## Defining simple data types

```
data Bool : Set where
  true  : Bool
  false : Bool
```

A new data type definition begins with the keyword `data` followed
by the name of the data type we are defining (`Bool` in this case)
and by its signature. The signature of `Bool` states that `Bool` is
an Agda `Set`, that is the simplest form for data type we can
define. In later sections we will define increasingly more complex
data types having more sophisticated signatures.

After the signature is the keyword `where` followed by a list of
**constructors**. For a simple data type like `Bool`, the
constructors effectively enumerate all the possible values of that
type. In this case, the only values of type `Bool` are `true` and
`false`.

It is important to stress that a new data type defines two distinct
entities: a new type name (`Bool`) which is different from any other
type that has been previously defined; a set of values of that type,
which is the smallest set of terms that can be built using the
provided constructors. When we say "value" we mean an expression
that cannot be reduced any further. However, there can be
expressions that are different from `true` and `false` and yet that
happen to have type `Bool` because, once evaluated, they yield a
value that is either `true` or `false`.

## Defining functions using pattern matching

Let us now define the function that *negates* a boolean value. Its
type is

```
not : Bool -> Bool
```

and its definition is given by cases on all the boolean values:

```
not true  = false
not false = true
```

Note that we are providing several *equations* for `not`, one for
each possible constructor for `Bool`, along with a corresponding
expression (on the right hand side of the `=` sign) showing what the
function yields when applied to a particular boolean value. As
always when we use the symbol `=`, we are telling Agda that `not
true` is definitionally equal to `false` and that `not false` is
definitionally equal to `true`. These terms are interchangeable and
one may be used where the other is expected.

We can ask Agda to *infer* the type of an application such as `not
true` or `not false` by hitting `C-c C-d`. In both cases Agda
answers `Bool`, meaning that both `not true` and `not false` are
expressions of type `Bool`, namely expressions that, once evaluated,
yield either `true` or `false`. In fact, we can also ask Agda to
evaluate the application of `not` to a boolean value by hitting `C-c
C-n` (the `n` in `C-n` abbreviates "normalize", which is the
technical term to indicate the evaluation process). We see that `not
true` evaluates to `false` and `not false` evaluates to `true`, in
accordance with the definition of `not`.

We will extensively use this style of defining functions by case
analysis on their arguments. In fact, Agda provides a convenient
facility for generating all the cases we have to consider in an
interactive way by starting from an *incomplete* definition of `not`
(as usual, we use indices such as ₁ and ₂ to distinguish multiple
definitions of the same function so that they are not in conflict
with each other).

   not₁ : Bool -> Bool
   not₁ x = ?

We can place the question mark `?` anywhere an expression is
expected and we do not know yet which expression it should be. Once
we have done that, by loading the file with `C-c C-l` the question
mark turns into a **hole**.

```
not₁ : Bool -> Bool
not₁ x = {!!}
```

By placing the cursor in the hole and hitting `C-c C-,` we can ask
Agda for help on how to proceed. Agda will tell us that we are
supposed to fill the hole with an expression of type `Bool` and also
that, in order to do so, we have at our disposal a value `x`, the
argument of `not₁`, which is also of type `Bool`. Since the result
of `not₁` *depends* on `x`, we have to perform a case analysis on it
by hitting `C-c C-c` and entering `x`. Agda knows that `x` is of
type `Bool` and that the only values of that type are `true` and
`false`, so Agda will create two equations corresponding to the two
cases we have to handle.

```
not₂ : Bool -> Bool
not₂ true  = {!!}
not₂ false = {!!}
```

We now have two holes to fill with expressions of type `Bool`. When
there is more than one hole, we can use `C-c C-f` and `C-c C-b` to
move forward and backward from one hole to the next or to the
previous one. By placing the cursor in the first hole we can enter
`false` followed by `C-c C-SPACE` to fill the hole with the provided
expression. Once we've also filled the second hole with `true` we
have completed the definition of `not₂`.

As an example of boolean function on two arguments, let us now
define the boolean conjunction.

```
and : Bool -> Bool -> Bool
and true  y = y
and false _ = false
```

Since `true` is the unit of boolean conjunction, when the first
argument of `and` is `true` the result is just the second
argument. Since `false` is the absorbing element of the boolean
conjunction, when the first argument of `and` is `false` the result
is simply `false` regardless of the second argument. Since the
second argument is not used in the second equation, we replace it
with an undeerscore `_`. It is not necessary to do so, but using
underscores on the left hand side of equations sometimes helps us
keeping the code clean and easier to read, highlighting the fact
that some arguments are not used in some cases.

We can ask Agda to evaluate `and` applied to some inputs to convince
ourseleves that the function behaves as expected. For example, `and
true true` evaluates to `true`, whereas `and false true` evaluates
to `false`.

Note that the above definition of `and` is not the only way to
define boolean conjunction. In fact, we could as well provide four
equations, one for each combination of inputs:

```
and₁ : Bool -> Bool -> Bool
and₁ true  true  = true
and₁ true  false = false
and₁ false true  = false
and₁ false false = false
```

As usual, there are many different ways in which functions can be
defined. However, in Agda this is more important than ever because
the way functions are defined may heavily affect how we prove
properties about them, as we will see shortly.

## Infix notation

Agda applications can be arbitrarily nested. For example, we can
express the conjunction of `true` with the result of the conjunction
of `true` and `false` by means of the expression `and true (and true
false)` which evaluates to `false`. This notation, in which a
function application is denoted by the function *followed by* its
arguments, is sometimes called **prefix** notation and is widespread
in most programming languages. However, it is occasionally desirable
to introduce a more lightweight and possibly more familiar notation
for function applications whereby a function with two arguments is
placed *in between* its arguments. Agda provides a sophisticated
mechanism to define such notation, in which the programmer specifies
the syntactic location of the arguments of a function by means of
underscores. For example, the following is an alternative, but fully
equivalent definition of `and` as the binary operator `&&` as found
in other programming languages.

```
_&&_ : Bool -> Bool -> Bool
true  && y = y
false && _ = false
```

With this definition in place, we can write e.g. `true && (true &&
false)` instead of `and true (and true false)`. The two underscores
in `_&&_` are still part of the name of the function we are
defining, although they are omitted when `&&` is used as an infix
operator. We can still refer to `&&` as a function by explicitly
writing the underscores. For example, `_&&_ true (_&&_ true false)`
is yet another way of writing `true && (true && false)`.

A problem remains in that it is still not possible to write an
expression such as `true && true && false`. The problem here is that
Agda does not know whether this expression is meant to be
interpreted as `true && (true && false)` or as `(true && true) &&
false`. We can provide this information by means of a *fixity
declaration* of the form

```
infixl 6 _&&_
```

telling Agda that `&&` is meant to be interpreted as a
*left-associative* operator with priority `6`. We would use `infixr`
for declaring *right-associative* operators and just `infix` for
declaring operators that are neither left- nor right-associative
(typically, these will be operators with one or more than two
operands).

## Exercises

1. Redefine `and` interactively by case splitting on its first argument.
2. Redefine `and` interactively by case splitting on its second argument.
3. Define the function `_||_ : Bool -> Bool -> Bool` that computes
   the *disjunction* of two boolean values. Make sure that the
   function behaves as expected by testing it on all possible
   inputs.
4. Provide a fixity declaration for `_||_` so that it is left
   associative and has priority smaller than that of `&&`. Use `C-c
   C-n` to convince yourself that the priorities given to `&&` and
   `||` work as expected.
5. Define the function `xor : Bool -> Bool -> Bool` that computes
   the exclusive or of two boolean values. Is it possible to define
   `xor` using just two equations?

```
-- EXERCISE 1
and₂ : Bool -> Bool -> Bool
and₂ x true  = x
and₂ _ false = false

-- EXERCISE 3
_||_ : Bool -> Bool -> Bool
_||_ true  _ = true
_||_ false y = y

-- EXERCISE 4
infixl 5 _||_

-- the value of false && true || true can be either true or false
-- depending on the priority given to && and ||. If && has greater
-- priority than ||, we have
--
--   false && true || true = (false && true) || true
--                         = false || true
--                         = true
--
-- Conversely, if || has greater priority than &&, we have
--
--   false && true || true = false && (true || true)
--                         = false && true
--                         = false

-- EXERCISE 5
xor : Bool -> Bool -> Bool
xor true  y = not y
xor false y = y
```
{:.solution}
