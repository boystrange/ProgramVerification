---
title: Main
---

This module imports **everything**, so that Agda can generate the
markdown files for all of the sources.

```agda
-- LECTURE 1
import Demo
import Setup
import Lambda
import Interactive

import InsertionSort

-- non terminating functions, using measures, intrinsic verification
import QuickSort

-- Binary search trees

-- example of Dan Licata (balanced trees?)

-- Regular expression matching (inference systems)

-- LIBRARY
import Library

-- TEST PAGE
import TestPage
```
