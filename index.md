---
title: Introduction to Program Verification in Agda
---

[GO TO THE TABLE OF CONTENTS](pages/Main.html){:.table-of-contents}

## Summary of Emacs shortcuts

| Command              | Action                                     |
|----------------------|--------------------------------------------|
| `C-c C-l`            | Load the current file                      |
| `C-c C-d expression` | Show the type of `expression`              |
| `C-c C-n expression` | Normalize `expression`                     |
| `C-c C-c argument`   | Perform case analysis on `argument`        |
| `C-c C-,`            | Show goal and context                      |
| `C-c C-f`            | Move forward to the next goal              |
| `C-c C-b`            | Move backward to the previous goal         |
| `C-c C-r`            | Refine the current hole                    |
| `C-c C-SPACE`        | Fill the hole with the provided expression |

## Ligatures and Unicode characters

These pages make use of the [Fira
Code](https://github.com/tonsky/FiraCode) font to display Agda
code. This font is particularly well suited for writing programs
since it supports a number of **ligatures** that make it possible to
display certain character sequences as if they were a single
glyph. A recurring example of ligature is that combining the
character `-` (the minus sign) followed by the character `>` (the
"greater than" sign), which in most fonts is displayed simply as
`-``>` whereas using Fira Code it is displayed as `->`. In other
circumstances, when there is no sequence of characters that produces
the desired ligature, we will use **Unicode characters**. A typical
example is that of the character U+2115 corresponding to the glyph
`ℕ`, which normally denotes the set of natural numbers.

The use of ligatures and of Unicode characters makes the code easier
and more pleasant to read, but it may make it more difficult to type
as it is not always clear which sequence of characters may produce a
given ligature or glyph. One possibility is to **cut and paste** the
desired symbols from these pages. Alternatively, when editing Agda
scripts in an editor that supports Agda (and that is possibly
configured to use Fira Code), special symbols can be entered by
typing particular sequences of characters. Below is a summary of the
ligatures and Unicode symbols that occur most frequently in these
pages. The [Fira Code](https://github.com/tonsky/FiraCode) page
contains a full table listing all of the ligatures supported by the
font.

| **Symbol**         | **Typed with**           |
|:-------------------|--------------------------|
| `->`               | `-``>`                   |
| `==` and `!=`      | `=``=` and `!``=`        |
| `<=>`              | `<``=``>`                |
| `<=`               | `<``=`                   |
| `<>`               | `<``>`                   |
| `ℕ`                | `\bN`                    |
| `∀` and `∃`        | `\all` and `\ex`         |
| `⟨` and `⟩`        | `\langle` and `\rangle`  |
| `λ`                | `\lambda`                |
| `₀`, `₁`, `₂`, ... | `\_0`, `\_1`, `\_2`, ... |
| `∘`                | `\circ`                  |
| `++`               | `+``+`                   |
| `∧` and `∨`        | `\and` and `\or`         |
| `⊤` and `⊥`        | `\top` and `\bot`        |
| `¬`                | `\neg`                   |
| `Σ`                | `\Sigma`                 |
| `×`                | `\x`                     |
| `⁺`                | `\^+`                    |

## References

This course material is partially based on and inspired from the
following courses, books and notes.

* Dan Licata, [Programming and Proving in
  Agda](https://www.cs.cmu.edu/~drl/teaching/oplss13/), Oregon
  Programming Languages Summer School, 2013.
* Samuel Mimram, [Program =
  Proof](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf),
  independently published, 2020.
* Peter Selinger, [Lectures on
  Agda](https://www.mathstat.dal.ca/~selinger/agda-lectures/),
  Dalhousie University, 2021.
* Aaron Stump, [Verified Functional Programming in
  Agda](http://www.morganclaypoolpublishers.com/catalog_Orig/product_info.php?cPath=24&products_id=908),
  ACM Books, 2016.
* Phil Wadler, Wen Kokke and Jeremy G. Siek, [Programming Language
  Foundations in Agda](https://plfa.github.io), independently
  published, 2019.

## Copyright

The course material in this site has been posted for your personal
educational use only. Copying course material from this site for
distribution (e.g. uploading material to a commercial third-party or
public website, or otherwise sharing these materials with people who
are not part of the class) may be a violation of Copyright law. If
you have questions regarding the use of materials from this site,
please contact the instructor.
