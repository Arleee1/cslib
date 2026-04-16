/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.Models.Comparison
public import Mathlib.Data.List.Infix

@[expose] public section

/-!
# Naive pattern search

In this file we define naive pattern search in the `Comparison` query model.

## Main definitions

- `prefixMatch`: checks whether a pattern is a prefix of some text.
- `naivePatternSearch`: returns the first start index of a contiguous match.
-/

namespace Cslib

namespace Algorithms

open Prog

open Comparison in
/--
`prefixMatch pat txt` compares `pat` against the beginning of `txt`, one character at a time.
-/
def prefixMatch (pat txt : List α) : Prog (Comparison α) Bool := do
  match pat, txt with
  | [], _ =>
    return true
  | _ :: _, [] =>
    return false
  | p :: ps, t :: ts =>
    let cmp : Bool ← compare p t
    if cmp then
      prefixMatch ps ts
    else
      return false

open Comparison in
/--
`naivePatternSearchFrom pat txt i` returns the first index `j >= i` such that
`pat` is a prefix of the suffix of `txt` starting at `j`.

If no such index exists, this returns the current remaining-text boundary,
which is `i + txt.length` at that recursion point.
-/
def naivePatternSearchFrom (pat txt : List α) (i : Nat) : Prog (Comparison α) Nat := do
  match pat with
  | [] =>
    return i
  | _ :: _ =>
    match txt with
    | [] =>
      return i
    | _ :: ts =>
      let found ← prefixMatch pat txt
      if found then
        return i
      else
        naivePatternSearchFrom pat ts (i + 1)

open Comparison in
/--
`naivePatternSearch pat txt` returns the 0-based start index of the first match of
`pat` in `txt`.

If no match exists, this returns `txt.length`.
-/
def naivePatternSearch (pat txt : List α) : Prog (Comparison α) Nat :=
  naivePatternSearchFrom pat txt 0

section Correctness

theorem prefixMatch_eval [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).eval Comparison.natCost = pat.isPrefixOf txt := by
  induction pat generalizing txt with
  | nil =>
      simp [prefixMatch]
  | cons p ps ih =>
      cases txt with
      | nil =>
          simp [prefixMatch]
      | cons t ts =>
          by_cases h : p == t
          · simp [prefixMatch, List.isPrefixOf, h, ih]
          · simp [prefixMatch, List.isPrefixOf, h]

private lemma patternSearchSpec_nil [BEq α] (txt : List α) :
    PatternSearch ([] : List α) txt = 0 := by
  simp [PatternSearch]

private lemma patternSearchSpec_cons_nil [BEq α] (p : α) (ps : List α) :
    PatternSearch (p :: ps) ([] : List α) = 0 := by
  simp [PatternSearch]

private lemma patternSearchSpec_cons_cons [BEq α] (p t : α) (ps ts : List α) :
    PatternSearch (p :: ps) (t :: ts) =
      if (p :: ps).isPrefixOf (t :: ts) then
        0
      else
        PatternSearch (p :: ps) ts + 1 := by
  rw [PatternSearch]
  simp only [reduceCtorEq, ↓reduceIte, List.tails]
  rw [List.dropLast_cons_of_ne_nil (by
    cases ts <;> simp [List.tails]), List.findIdx_cons]
  simp [PatternSearch]

private lemma naivePatternSearchFrom_eval [BEq α] (pat txt : List α) (i : Nat) :
    (naivePatternSearchFrom pat txt i).eval Comparison.natCost =
      i + PatternSearch pat txt := by
  cases pat with
  | nil =>
      rw [naivePatternSearchFrom, patternSearchSpec_nil]
      simp
  | cons p ps =>
      induction txt generalizing i with
      | nil =>
          rw [naivePatternSearchFrom, patternSearchSpec_cons_nil]
          simp
      | cons t ts ih =>
          by_cases h : (p :: ps).isPrefixOf (t :: ts)
          · rw [patternSearchSpec_cons_cons, if_pos h]
            simp [naivePatternSearchFrom, prefixMatch_eval, h]
          · rw [patternSearchSpec_cons_cons, if_neg h]
            simp [naivePatternSearchFrom, prefixMatch_eval, h, ih, Nat.add_assoc, Nat.add_comm]

theorem naivePatternSearch_eval [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).eval Comparison.natCost = PatternSearch pat txt := by
  rw [naivePatternSearch]
  convert naivePatternSearchFrom_eval pat txt 0 using 1
  simp

end Correctness

end Algorithms

end Cslib
