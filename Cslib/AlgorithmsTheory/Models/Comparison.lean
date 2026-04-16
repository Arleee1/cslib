/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.QueryModel
public import Mathlib.Data.List.Infix

@[expose] public section

/-!
# Query Type for Comparisons

In this file we define a query type `Comparison` for comparison based algorithms, whose sole query
`compare` compares two arguments. It further defines a model `Comparison.natCost` for this query.
--

## Definitions

- `Comparison`: A query type for comparison based algorithms.
- `Comparison.natCost`:  A model for this query with costs in `ℕ`.
- `PatternSearch`: First-occurance pattern searching definition.

-/

namespace Cslib

namespace Algorithms

open Prog

/--
A query type for comparing elements. It supports exactly one query
`compare x y` which returns `true` if `x` is equal to `y`
and returns `false` otherwise.
-/
inductive Comparison (α : Type*) : Type → Type _ where
  | compare (x y : α) : Comparison α Bool


/-- A model of the `Comparison` query type that assigns the cost as the number of queries. -/
@[simps]
def Comparison.natCost [BEq α] : Model (Comparison α) ℕ where
  evalQuery
    | .compare x y => x == y
  cost _ := 1

/--
`PatternSearch pat txt` returns the first starting position in `txt` such that
`pat` is a prefix of `txt` starting there. For nonempty `pat`, failure returns
`txt.length`. For empty `pat`, the result is always `0`.

TODO: move definition
-/
def PatternSearch [BEq α] (pat txt : List α) : Nat :=
  if pat = [] then
    0
  else
    (txt.tails.dropLast).findIdx fun suffix => pat.isPrefixOf suffix

end Algorithms

end Cslib
