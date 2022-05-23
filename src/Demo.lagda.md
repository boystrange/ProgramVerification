---
title: A taste of Agda
---

<!--
```agda
open import Equality
open import Nat
```
-->

To get a taste of Agda, let us write a `fibo` function that computes
the $k$-th number in the sequence of Fibonacci, that is the sequence

$$
  0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, \dots
$$

that starts with 0 followed by 1 and such that each subsequent
number is the sum of the previous two. For example, we expect `fibo`
to return 55 when it is applied to 10, since 55 is the 11th number
in the sequence. The easiest implementation of `fibo` in Agda is
shown below. Note that the program makes use of natural numbers,
which must be suitably defined and imported for this program to
correctly type check and compile.

```agda
fibo : ℕ -> ℕ
fibo 0               = 0
fibo 1               = 1
fibo (succ (succ k)) = fibo k + fibo (succ k)
```

Once this script is loaded, we can ask Agda to compute the result of
applying `fibo` to some numbers. By pressing `CTRL-C` followed by
`CTRL-N` and then entering 11 we obtain 55, as expected.

It is a known fact that the shown implementation of `fibo` is very
inefficient. In fact, the time for computing the $k$-th Fibonacci
number is exponential in $k$. We can propose a more efficient,
albeit slightly more complex function that computes the $k$-th
Fibonacci number in linear time, as follows.

```agda
fibo-gen : ℕ -> ℕ -> ℕ -> ℕ
fibo-gen m n 0               = m
fibo-gen m n 1               = n
fibo-gen m n (succ (succ k)) = fibo-gen n (m + n) (succ k)

fast-fibo : ℕ -> ℕ
fast-fibo = fibo-gen 0 1
```

The `fast-fibo` function is just a wrapper for the auxiliary
`fibo-gen` function, which takes three arguments: `m` and `n`, which
are supposed to be two subsequent numbers in the Fibonacci sequence,
and then an index `k` which represents the number of steps to make
in the sequence, starting from `m` and `n`, in order to reach the
desired number. When `k` is 0, the desired number is just `m`. When
`k` is 1, the desired number is just `n`.  When `k` is greater than
one, we recursively apply `fibo-gen` so that `m` becomes `n`, `n`
becomes the sum of the (old) `m` and of the (old) `n`, and `k` is
decreased by one. That is, `fibo-gen` is basically a functional
implementation of the classical loop that finds the desired number
in the Fibonacci sequence by using (and updating) two auxiliary
variables `m` and `n` initialized with 0 and 1.

Now, since `fast-fibo` (and particularly `fibo-gen` on which it
relies) is substantially more complex than `fibo`, we may wonder
whether it is in fact equivalent to `fibo`. We may perform a few
test asking Agda to evaluate `fast-fibo`, but these tests are
**necessarily finite**. The only way to be absolutely sure that
`fibo` and `fast-fibo` are the same function is by **proving** that
they are equivalent.

It is not too difficult to come up with a pen-and-paper proof that
`fibo` and `fast-fibo` are indeed equivalent, but the doubt might
remain that the proof could contain a mistake. After all, we're
humans and all humans make mistakes. Here is where Agda comes to the
rescue, in that it provides us with some tools for **checking**
whether an equivance proof for `fibo` and `fast-fibo` is valid. Even
more surprisingly, the equivalence proof turns out to be a
collection of functions written in the same language in which we
have implemented `fibo` and `fast-fibo`.

Below are two functions, called `lemma` and `theorem` that prove the
equivalence of `fibo` and `fast-fibo`. For the time being they look
like almost random sequences of meaningless symbols. In this course
we will learn how to write such proofs with the help of the
interactive features of Agda. For the sake of this quick
introduction, though, it may be worth to notice that in the
**types** of these functions we recognize occurrences of `∀` (the
*universal quantifier*), `->` (*logical implication*), and `==`
(*propositional equality*). In particular the type of `theorem`
specifies that, for every natural number `k`, the value resulting
from the application `fast-fibo k` is the same value resulting from
the application `fibo k`.

```agda
lemma : ∀(k i : ℕ) -> fibo-gen (fibo k) (fibo (succ k)) i == fibo (i + k)
lemma k 0 = refl
lemma k 1 = refl
lemma k (succ (succ i)) =
  begin
    fibo-gen (fibo (succ k)) (fibo k + fibo (succ k)) (succ i) ==⟨⟩
    fibo-gen (fibo (succ k)) (fibo (succ (succ k))) (succ i)
      ==⟨ lemma (succ k) (succ i) ⟩
    fibo (succ i + succ k) ==⟨⟩
    fibo (succ (i + succ k))
      ==⟨ cong (λ x -> fibo (succ x)) (+-commutative i (succ k)) ⟩
    fibo (succ (succ k + i)) ==⟨⟩
    fibo (succ (succ (k + i)))
      ==⟨ cong (λ x -> fibo (succ (succ x))) (+-commutative k i) ⟩
    fibo (succ (succ (i + k)))
  end

theorem : ∀(k : ℕ) -> fast-fibo k == fibo k
theorem k =
  begin
    fast-fibo k    ==⟨⟩
    fibo-gen 0 1 k ==⟨ lemma 0 k ⟩
    fibo (k + 0)   ==⟨ cong fibo (symm (+-zero k)) ⟩
    fibo k
  end
```

By checking that these functions adhere to the types we've given
them, Agda certifies that `fibo` and `fast-fibo` are equivalent. So,
from now on we can safely use whichever function is more convenient
depending on the context, preferring `fibo` or `fast-fibo` depending
on whether readability or performance is more important.

## Homework

1. Let $F_i$ be the $i$-th Fibonacci number, defined by the equations

   $$
     F_0 = 0
     \qquad
     F_1 = 1
     \qquad
     F_{i+2} = F_i + F_{i+1}
   $$

   Using pencil and paper, prove that `fibo-gen` $F_i$ $F_{i+1}$ $k$
   = $F_{i+k}$ by induction on $k$.

   > By induction on $k$. There are two base cases: when $k = 0$,
   > then `fibo-gen` $F_i$ $F_{i+1}$ $0$ = $F_i$ = $F_{i+k}$; when
   > $k = 1$, then `fibo-gen` $F_i$ $F_{i+1}$ $1$ = $F_{i+1}$ =
   > $F_{i+k}$. In the inductive case we have $k > 1$. By definition
   > of `fibo-gen` we have `fibo-gen` $F_i$ $F_{i+1}$ $k$ =
   > `fibo-gen` $F_{i+1}$ $F_{i+2}$ $(k-1)$. Using the induction
   > hypothesis we conclude `fibo-gen` $F_{i+1}$ $F_{i+2}$ $(k-1)$ =
   > $F_{i+k}$.
   {:.solution}
