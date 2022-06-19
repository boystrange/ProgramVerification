---
title: Logical connectives
---

The logic we have been using so far is based on a small set of
operators that correspond to a limited set of Agda types:

* The arrow or function type corresponds to **logical implication**:
  a proof of `A -> B` is a function that, applied to a proof of `A`,
  yields a proof of `B`.
* The dependent arrow type corresponds to **universal
  quantification**: a proof of `(x : A) -> B` is a function that,
  applied to an element `x` of type `A`, yields a proof of `B`
  (where `x` may occur in `B`).
* The **equality predicate** `E == F` is the type of proofs showing
  that `E` is equal to `F`.

In general, we will need a richer set of logical connectives in
order to prove interesting properties of programs. As it turns out,
all the other connectives can be defined in terms of the
aforementioned types or as suitable data types. In this chapter 

* **Conjunction** `∧`
* **Disjunction** `∨`
* **Truth** `⊤`
* **Falsity** `⊥`
