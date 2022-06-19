---
title: Natural numbers
---

<!--
```agda
{-# OPTIONS --allow-unsolved-metas #-}

module Chapter.NaturalNumbers where

open import Equality
open import Equality.Reasoning
```
-->

In this section we define the data type of natural numbers and some
operations on them. We then prove some fundamental properties of
these operations.

The main challenge we have to face in defining the data type of
natural numbers is that there are infinitely many of them. So, we
cannot just enumerate all the natural numbers as we have done for
the values `true` and `false` of type `Bool`. However, we can
provide a finite number of constructors with which we can build
increasingly large natural numbers by recalling that any natural
number other than 0 is the successor of another (smaller) natural
number, its predecessor. This intuition leads to the definition of
natural numbers as the smallest set of terms that have either the
form `zero` or `succ x` where `x` is a natural number. The
corresponding data type is the following.

```agda
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ
```

According to this definition, `zero` is a natural number by itself,
whereas `succ` is a function that yields a natural number when it is
applied to another natural number. As a consequence, all of the
following terms are natural numbers of type `ℕ`, as you can easily
verify using `C-c C-d`.

    zero             -- the natural number 0
    succ zero        -- the natural number 1
    succ (succ zero) -- the natural number 2
    succ ...         -- ...and so on

The fact that every natural number, no matter how large, can be
constructed with repeated applications of just two constructors
`zero` and `succ` will be convenient in the following, when we will
define functions by case analysis on arguments that have type
`ℕ`. However, it would be helpful to make Agda recognize the
standard positional notation using sequences of digits. We can do so
by means of the following directive

```agda
{-# BUILTIN NATURAL ℕ #-}
```

telling Agda that any sequence of decimal digits such as `1234`
should be expanded into 1234 subsequent applications of `succ` to
`zero`. We can verify this property (on reasonably small numbers) by
writing theorems like the following one:

```agda
three-eq : 3 == succ (succ (succ zero))
three-eq = refl
```

## Basic operations on natural numbers

Let us now define the addition on natural numbers.

```agda
_+_ : ℕ -> ℕ -> ℕ
zero   + y = y
succ x + y = succ (x + y)
```

Note that the function `_+_` is defined by case analysis on its
first argument. If the first argument is `zero`, then the result is
the second argument. If the first argument is the successor of `x`,
then the result is the successor of the recursive application of
`_+_` to `x` and `y`. We can verify that `_+_` behaves as expected
either by normalizing some expressions such as `1 + 2` using `C-c
C-n` or by proving some theorem such as the following:

```agda
one-plus-two : 1 + 2 == 3
one-plus-two = refl
```

We can define multiplication in terms of addition, thus:

```agda
_*_ : ℕ -> ℕ -> ℕ
zero   * y = zero
succ x * y = y + (x * y)
```

For example, we have:

```agda
two-times-three : 2 * 3 == 6
two-times-three = refl
```

Let us provide two fixity declarations for `+` and `*` so that they
are left associative and `*` has precedence over `+`.

```agda
infixl 6 _+_
infixl 7 _*_
```

We can now verify that Agda applies the correct precedence by
proving that the value of `1 + 2 * 3` is `7` and not `9`:

```agda
one-plus-two-times-three : 1 + 2 * 3 == 7
one-plus-two-times-three = refl
```

## Associativity of `+` and congruence

By declaring that `+` is left associative we are only telling Agda
that an expression such as `1 + 2 + 3` is to be interpreted as `(1 +
2) + 3`, not that addition is an associative operator. We can
*prove* that `+` is indeed associative by defining the following
function:

```agda
+-assoc : (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-assoc x y z = {!!}
```

This function takes three natural numbers `x`, `y` and `z` as
arguments and yields a proof that `x + (y + z)` and `(x + y) + z`
are equal. As we have seen for booleans, also for natural numbers we
usually need to perform case analysis on one or more arguments in
order to prove a property like `+-assoc`. However, it may not be
obvious to decide *on which* argument we should do case analysis
on. A general rule of thumb that works in many cases is to look at
the goal that we want to prove, `x + (y + z) == (x + y) + z` and to
rank the variables according to the number of times case analysis is
performed on them by the operators that occur therein. We know that
`+` performs case analysis on its left operand, so in the above type
the variable `x` is ranked 2 (case analysis on `x` is performed
twice, on both sides of `==`), the variable `y` is ranked 1 (case
analysis on `y` is performed only once, on the left hand side of
`==`) and the variable `z` is ranked 0 (case analysis on `z` is
never performed). By doing case analysis on `x` we obtain:

```agda
+-assoc₁ : (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-assoc₁ zero     y z = {!!}
+-assoc₁ (succ x) y z = {!!}
```

The type of the first hole is `y + z == y + z`, which results from
normalizing `x + (y + z) == (x + y) + z` when `x` is replaced by
`zero`. So, it can be filled with `refl`.

```agda
+-assoc₂ : (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-assoc₂ zero     y z = refl
+-assoc₂ (succ x) y z = {!!}
```

The remaining hole has type `succ (x + (y + z)) == succ ((x + y) +
z)` and is a bit more difficult to handle. It requires us to provide
a proof that the successor of `x + (y + z)` is equal to the
successor of `(x + y) + z`. Observe that we can obtain a proof of
<!----> `x + (y + z) == (x + y) + z` by recursively applying
`+-assoc₂` to `x`, `y` and `z`. What is now missing is the property
that if we apply a function - `succ` in this case - to equal
arguments, we obtain equal results. This is a **congruence**
property of equality with respect to function application which is
provided by the `cong` function in the `Equality` module: if `x` and
`y` are elements of type `A`, `f` is a function of type `A -> B` and
`eq` is a proof of `x == y`, then `cong f eq` yields a proof of `f x
== f y`. Using `cong` we can complete the proof that `+` is
associative, thus:

```agda
+-assoc₃ : (x y z : ℕ) -> x + (y + z) == (x + y) + z
+-assoc₃ zero     y z = refl
+-assoc₃ (succ x) y z = cong succ (+-assoc₃ x y z)
```

## Commutativity of `+` and equational reasoning

Proving that `+` is also commutative involves a little more work. As
it turns out it is useful to first prove two auxiliary properties
that will come handy in due time. The first property asserts that
`zero` is a right unit for `+`.

```agda
+-unit-r : (x : ℕ) -> x == x + zero
+-unit-r zero     = refl
+-unit-r (succ x) = cong succ (+-unit-r x)
```

Note that the fact that `zero` is a left unit for `+` follows from
the very definition of `+` since `zero + x` is definitionally equal
to `x`.

```agda
+-unit-l : (x : ℕ) -> x == zero + x
+-unit-l x = refl
```

The second auxiliary property asserts that an application of `succ`
in a sum can be shifted from one operand to the other without
affecting the result.

```agda
+-succ : (x y : ℕ) -> (succ x) + y == x + (succ y)
+-succ zero     y = refl
+-succ (succ x) y = cong succ (+-succ x y)
```

We are now ready to prove the commutativity property of `+`.

```agda
+-comm : (x y : ℕ) -> x + y == y + x
+-comm x y = {!!}
```

As usual, we proceed by performing case analysis on `x`, which
yields the following two cases to deal with:

```agda
+-comm₁ : (x y : ℕ) -> x + y == y + x
+-comm₁ zero     y = {!!}
+-comm₁ (succ x) y = {!!}
```

Concerning the first case, we have to provide a proof of `y == y +
zero`. This is precisely the property that we called `+-unit-r`
applied to the variable `y`.

```agda
+-comm₂ : (x y : ℕ) -> x + y == y + x
+-comm₂ zero     y = +-unit-r y
+-comm₂ (succ x) y = {!!}
```

To close the remaining hole it is convenient to use **equational
reasoning**, that is a (definable) Agda construct that allows us to
perform an arbitrary number of rewritings by means of equalities and
possibly other relations. In its simplest form, an equational
reasoning block has the form

    begin
      E₁ ==⟨ P₁ ⟩
      E₂ ==⟨ P₂ ⟩
      ...
      Eₙ
    end

where `E₁ == Eₙ` is the equality that we want to prove and each `Pᵢ`
justifies a single rewriting step from `Eᵢ` to the subsequent
expression. Let's see how we can close the commutativity proof of
`+` using an equational reasoning block.

```agda
+-comm₃ : (x y : ℕ) -> x + y == y + x
+-comm₃ zero     y = +-unit-r y
+-comm₃ (succ x) y =
  begin
    (succ x) + y ==⟨ refl ⟩                    -- (1)
    succ (x + y) ==⟨ cong succ (+-comm₃ x y) ⟩ -- (2)
    succ (y + x) ==⟨ refl ⟩                    -- (3)
    (succ y) + x ==⟨ +-succ y x ⟩              -- (4)
    y + (succ x)
  end
```

We use the number in comments to reference each step in the block:

1. Here we are using reflexivity to rewrite `(succ x) + y` to `succ
   (x + y)`, according to the definition of `+`.
2. Next, we recursively apply `+-comm₃` to `x` and `y` to obtain a
   proof of `x + y == y + x` and consequently a proof that the
   respective successors are equal by means of `cong`.
3. Here we use reflexivity once more to rewrite `succ (y + x)` into
   `(succ y) + x`, again using the definition of `+` (but from right
   to left!).
4. Finally, we use the auxiliary property `+-succ` proved before to
   shift the application of `succ` from the left to the right
   operand.

We conclude the discussion of this example with three observations.
First, it may not be obvious *a priori* that `+-unit-r` and `+-succ`
are the right auxiliary properties required to prove `+-comm`. In
fact, one usually realizes which auxiliary properties are needed
while proving the main result. Second, the applications of
reflexivity in steps (1) and (3) are superfluous. Since the terms
related by reflexivity are definitionally equal, Agda would also
accept a shorter equational reasoning block in which only steps (2)
and (4) are provided. Here we have chosen to be explicit in each
rewriting for the sake of clarity. In general, for complex rewriting
sequences it is usually a good idea to detail most steps.  Finally,
in this equational reasoning block we have systematically written
`(succ x)` (within parentheses) for emphasis, even though
parentheses would not be necessary in this case since function
application has higher precedence than any other operator (including
`+`). In the following we will usually omit unnecessary parentheses.

## Some properties of `*`

We conclude this chapter with the proof that multiplication is
associative. To this aim, we first prove that `*` distributes over
`+` on the right.

```agda
*-dist-r : (x y z : ℕ) -> (x + y) * z == x * z + y * z
*-dist-r zero y z = refl
*-dist-r (succ x) y z =
  begin
    (succ x + y) * z    ==⟨ refl ⟩
    succ (x + y) * z    ==⟨ refl ⟩
    z + (x + y) * z     ==⟨ cong (z +_) (*-dist-r x y z) ⟩
    z + (x * z + y * z) ==⟨ +-assoc z (x * z) (y * z) ⟩
    (z + x * z) + y * z ==⟨ refl ⟩
    succ x * z + y * z
  end
```

The proof is ordinary except for a small technical detail in the
application of congruence. In the third rewriting step we rewrite
<!----> `z + (x + y) * z` into `z + (x * z + y * z)` using a
recursive application of `*-dist-r`. However, the rewriting occurs
in the right operand of the outermost `+`. In principle, we could
justify this rewriting with the proof

    cong (λ u -> z + u) (*-dist-r x y z)

where the function `(λ u -> z + u)` describes the context in which
the rewriting takes place. Instead of defining this lambda
abstraction explicitly, we have written `(z +_)` which stands for
the function that takes an argument (say `u`) and yields `z + u`. In
this case, we have provided the infix operator `+` with just one of
the operands, leaving an underscore on the side from which we
abstract over the other one.

We are now ready to prove the associativity of `*`.

```agda
*-assoc : (x y z : ℕ) -> x * (y * z) == (x * y) * z
*-assoc zero y z = refl
*-assoc (succ x) y z =
  begin
    succ x * (y * z)    ==⟨ refl ⟩
    y * z + x * (y * z) ==⟨ cong (y * z +_) (*-assoc x y z) ⟩
    y * z + (x * y) * z   ⟨ *-dist-r y (x * y) z ⟩==
    (y + x * y) * z     ==⟨ refl ⟩
    (succ x * y) * z
  end
```

In the third step of equational reasoning block of this proof we see
an example of reverse rewriting, whereby we aim at rewriting <!---->
`y * z + (x * y) * z` into `(y + x * y) * z` using <!---->
`*-dist-r`. The difficulty here is that `*-dist-r` proves the
rewriting in the opposite direction. Of course, we could have
defined `*-dist-r` in such a way that its conclusion matches the
direction of the rewriting we want to perform in `*-assoc`, but in
general it may happen that we want to perform the opposite of a
rewriting we have already proved. In these cases, we can use the
symmetry property of equality to perform the desired rewriting. In
an equational reasoning block, we specify the use of symmetry by
using the reverse rewriting operator `E ⟨ P ⟩== E'` instead of the
usual `E ==⟨ P ⟩ E'`.

## Exercises

1. Define subtraction `_-_ : ℕ -> ℕ -> ℕ` so that `zero - x` is
   `zero` and verify its behavior using `C-c C-n`. Provide a fixity
   declaration for `-` so that is is left associative and has the
   same precedence as `+`.
2. Define the factorial function `fact : ℕ -> ℕ` and verify its
   behavior using `C-c C-n`.
3. Prove `*-unit-l` and `*-unit-r` showing that `1` is a left and
   right unit for `*`.
4. Prove `*-comm` showing that `*` is commutative.
5. Prove `*-dist-l` showing that `*` distributes over `+` on the
   left using `*-comm` and `*-dist-r`.
6. Define the exponentiation function `_^_ : ℕ -> ℕ -> ℕ` and
   provide a fixity declaration so that it is left associative and
   has higher precedence than `*`.
7. Prove that `x ^ m * x ^ n == x ^ (m + n)`. CONTROLLARE

```agda
-- EXERCISE 1

_-_ : ℕ -> ℕ -> ℕ
x      - zero   = x
zero   - succ y = zero
succ x - succ y = x - y

-- EXERCISE 2

fact : ℕ -> ℕ
fact zero     = 1
fact (succ x) = succ x * fact x

*-zero-r : (x : ℕ) -> 0 == x * 0
*-zero-r zero     = refl
*-zero-r (succ x) = *-zero-r x

-- EXERCISE 3

*-unit-l : (x : ℕ) -> 1 * x == x
*-unit-l x =
  begin
    1 * x     ==⟨ refl ⟩
    x + 0 * x ==⟨ refl ⟩
    x + 0       ⟨ +-unit-r x ⟩==
    x
  end

*-unit-r : (x : ℕ) -> x * 1 == x
*-unit-r zero     = refl
*-unit-r (succ x) = cong succ (*-unit-r x)

-- EXERCISE 4

*-succ : (x y : ℕ) -> x + x * y == x * succ y
*-succ zero y = refl
*-succ (succ x) y =
  begin
    succ x + (succ x * y) ==⟨ refl ⟩
    succ x + (y + x * y)  ==⟨ cong (succ x +_) {!!} ⟩
    succ x + (x * succ y) ==⟨ {!!} ⟩
    succ (x + x * succ y) ==⟨ cong succ {!!} ⟩
    succ (succ x * succ y) ==⟨ {!!} ⟩
    {!!}
  end

*-comm : (x y : ℕ) -> x * y == y * x
*-comm zero y     = *-zero-r y
*-comm (succ x) y =
  begin
    succ x * y ==⟨ refl ⟩
    y + x * y ==⟨ cong (y +_) (*-comm x y) ⟩
    y + y * x ==⟨ *-succ y x ⟩
    y * succ x
  end

-- EXERCISE 5

*-dist-l : (x y z : ℕ) -> x * (y + z) == x * y + x * z
*-dist-l x y z =
  begin
    x * (y + z)   ==⟨ *-comm x (y + z) ⟩
    (y + z) * x   ==⟨ *-dist-r y z x ⟩
    y * x + z * x ==⟨ cong (_+ z * x) (*-comm y x) ⟩
    x * y + z * x ==⟨ cong (x * y +_) (*-comm z x) ⟩
    x * y + x * z
  end

-- EXERCISE 6

infixl 8 _^_

_^_ : ℕ -> ℕ -> ℕ
x ^ zero = 1
x ^ succ n = x * x ^ n

-- EXERCISE 7

^-prop-1 : (x m n : ℕ) -> x ^ m * x ^ n == x ^ (m + n)
^-prop-1 x zero     n = *-unit-l (x ^ n)
^-prop-1 x (succ m) n =
  begin
    x ^ succ m * x ^ n  ==⟨ refl ⟩
    (x * x ^ m) * x ^ n   ⟨ *-assoc x (x ^ m) (x ^ n) ⟩==
    x * (x ^ m * x ^ n) ==⟨ cong (x *_) (^-prop-1 x m n) ⟩
    x * x ^ (m + n)
  end
```
