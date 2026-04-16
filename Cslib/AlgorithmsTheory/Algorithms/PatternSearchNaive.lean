/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.Models.Comparison
public import Mathlib.Data.List.Infix
public import Mathlib.Algebra.Order.Group.Nat

@[expose] public section

/-!
# Naive pattern search

In this file we define naive pattern search in the `Comparison` query model.
--

## Main definitions

- `prefixMatch`: checks whether a pattern is a prefix of some text.
- `naivePatternSearch`: returns the first start index of a contiguous match.

## Main results

- `prefixMatch_eval`: `prefixMatch` evaluates identically to List.isPrefixOf.
- `naivePatternSearch_eval`: `naivePatternSearch` evaluates identically to `PatternSearch`.
- `prefixMatch_time_complexity_upper_bound`: `prefixMatch` takes at most `pat.length` comparisons.
- `naivePatternSearch_time_complexity_upper_bound`: `naivePatternSearch` takes at most
    `pat.length * txt.length` comparisons.
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
  | nil => simp [prefixMatch]
  | cons p ps ih =>
    cases txt with
    | nil => simp [prefixMatch]
    | cons t ts => by_cases h : p == t <;> simp [prefixMatch, List.isPrefixOf, h, ih]

private lemma naivePatternSearchFrom_eval [BEq α] (pat txt : List α) (i : Nat) :
    (naivePatternSearchFrom pat txt i).eval Comparison.natCost =
      i + PatternSearch pat txt := by
  cases pat with
  | nil => simp [naivePatternSearchFrom, PatternSearch]
  | cons p ps =>
    induction txt generalizing i with
    | nil => simp [naivePatternSearchFrom, PatternSearch]
    | cons t ts ih =>
      have hPS : PatternSearch (p :: ps) (t :: ts) =
          if (p :: ps).isPrefixOf (t :: ts) then 0
          else PatternSearch (p :: ps) ts + 1 := by
        simp only [PatternSearch, reduceCtorEq, ↓reduceIte, List.tails]
        rw [List.dropLast_cons_of_ne_nil (by cases ts <;> simp [List.tails]), List.findIdx_cons]
        simp
      by_cases h : (p :: ps).isPrefixOf (t :: ts)
      · simp [hPS, h, naivePatternSearchFrom, prefixMatch_eval]
      · simp [hPS, h, naivePatternSearchFrom, prefixMatch_eval, ih, Nat.add_assoc, Nat.add_comm]

theorem naivePatternSearch_eval [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).eval Comparison.natCost = PatternSearch pat txt := by
  simp [naivePatternSearch, naivePatternSearchFrom_eval]

end Correctness

section TimeComplexity

theorem prefixMatch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).time Comparison.natCost ≤ pat.length := by
  induction pat generalizing txt with
  | nil => simp [prefixMatch]
  | cons p ps ih =>
    cases txt with
    | nil => simp [prefixMatch]
    | cons t ts =>
      by_cases h : p == t
      · simpa [prefixMatch, h, Nat.add_comm] using Nat.add_le_add_left (ih ts) 1
      · simp [prefixMatch, h]

private lemma naivePatternSearchFrom_time_complexity_upper_bound [BEq α]
    (pat txt : List α) (i : Nat) :
    (naivePatternSearchFrom pat txt i).time Comparison.natCost ≤ pat.length * txt.length := by
  cases pat with
  | nil => simp [naivePatternSearchFrom]
  | cons p ps =>
    induction txt generalizing i with
    | nil => simp [naivePatternSearchFrom]
    | cons t ts ih =>
      have hpre := prefixMatch_time_complexity_upper_bound (p :: ps) (t :: ts)
      cases heval : (prefixMatch (p :: ps) (t :: ts)).eval Comparison.natCost
      · simpa [naivePatternSearchFrom, heval, Nat.mul_succ, Nat.add_comm] using
          Nat.add_le_add hpre (ih (i + 1))
      · simpa [naivePatternSearchFrom, heval] using
          hpre.trans (Nat.le_mul_of_pos_right _ (by simp))

theorem naivePatternSearch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).time Comparison.natCost ≤ pat.length * txt.length := by
  simpa [naivePatternSearch] using naivePatternSearchFrom_time_complexity_upper_bound pat txt 0

end TimeComplexity

end Algorithms

end Cslib
