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
- `prefixMatch_time_complexity_upper_bound`: `prefixMatch` takes at most
  `min pat.length txt.length` comparisons.
- `naivePatternSearch_time_complexity_upper_bound`: `naivePatternSearch` takes at most
    `pat.length * (txt.length + 1 - pat.length)` comparisons.
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
    if pat.length ≤ txt.length then
      match txt with
      | [] =>
        return i
      | _ :: ts =>
        let found ← prefixMatch pat txt
        if found then
          return i
        else
          naivePatternSearchFrom pat ts (i + 1)
    else
      return i + txt.length

open Comparison in
/--
`naivePatternSearch pat txt` returns the 0-based start index of the first match of
`pat` in `txt`.

If no match exists, this returns `txt.length`.
-/
def naivePatternSearch (pat txt : List α) : Prog (Comparison α) Nat :=
  naivePatternSearchFrom pat txt 0

section Correctness

private lemma isPrefixOf_eq_false_of_length_lt [BEq α] :
    ∀ {pat txt : List α}, txt.length < pat.length → pat.isPrefixOf txt = false
  | [], _, h => by simp at h
  | _ :: _, [], _ => by simp [List.isPrefixOf]
  | p :: ps, t :: ts, h => by
      have htail : ts.length < ps.length := by simpa using h
      by_cases heq : p == t
      · simp [List.isPrefixOf, heq, isPrefixOf_eq_false_of_length_lt htail]
      · simp [List.isPrefixOf, heq]

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
    have hPS : ∀ txt : List α,
        PatternSearch (p :: ps) txt =
          match txt with
          | [] => 0
          | _ :: ts =>
              if (p :: ps).isPrefixOf txt then 0 else PatternSearch (p :: ps) ts + 1 := by
      intro txt
      cases txt with
      | nil => simp [PatternSearch]
      | cons t ts =>
        simp only [PatternSearch, reduceCtorEq, ↓reduceIte, List.tails]
        rw [List.dropLast_cons_of_ne_nil (by cases ts <;> simp [List.tails]), List.findIdx_cons]
        simp
    have hlt : ∀ txt : List α,
        txt.length < (p :: ps).length → PatternSearch (p :: ps) txt = txt.length := by
      intro txt
      induction txt with
      | nil =>
        intro hlen
        simp [PatternSearch]
      | cons t ts ih =>
        intro hlen
        have hfalse : (p :: ps).isPrefixOf (t :: ts) = false :=
          isPrefixOf_eq_false_of_length_lt hlen
        have htail : ts.length < (p :: ps).length := by
          exact lt_trans (Nat.lt_succ_self _) hlen
        rw [hPS]
        simp [hfalse, ih htail]
    induction txt generalizing i with
    | nil => simp [naivePatternSearchFrom, PatternSearch]
    | cons t ts ih =>
      have hdef :
          naivePatternSearchFrom (p :: ps) (t :: ts) i =
            if (p :: ps).length ≤ (t :: ts).length then
              (do
                let found ← prefixMatch (p :: ps) (t :: ts)
                if found then pure i else naivePatternSearchFrom (p :: ps) ts (i + 1))
            else
              pure (i + (t :: ts).length) := by
        rfl
      by_cases hlen : (p :: ps).length ≤ (t :: ts).length
      · have hlen' : ps.length ≤ ts.length := by simpa using hlen
        by_cases h : (p :: ps).isPrefixOf (t :: ts)
        · calc
            (naivePatternSearchFrom (p :: ps) (t :: ts) i).eval Comparison.natCost
                = ((do
                      let found ← prefixMatch (p :: ps) (t :: ts)
                      if found then pure i else naivePatternSearchFrom (p :: ps) ts (i + 1)
                    )).eval Comparison.natCost := by
                      rw [hdef]
                      simp [hlen']
            _ = i := by
                  simp [Prog.eval_bind, prefixMatch_eval, h]
            _ = i + PatternSearch (p :: ps) (t :: ts) := by
                  rw [hPS]
                  simp [h]
        · have hfound : (prefixMatch (p :: ps) (t :: ts)).eval Comparison.natCost = false := by
            simp [prefixMatch_eval, h]
          have hrec := ih (i + 1)
          calc
            (naivePatternSearchFrom (p :: ps) (t :: ts) i).eval Comparison.natCost
                = ((do
                      let found ← prefixMatch (p :: ps) (t :: ts)
                      if found then pure i else naivePatternSearchFrom (p :: ps) ts (i + 1)
                    )).eval Comparison.natCost := by
                      rw [hdef]
                      simp [hlen']
            _ = (naivePatternSearchFrom (p :: ps) ts (i + 1)).eval Comparison.natCost := by
                  simp [Prog.eval_bind, hfound]
            _ = i + 1 + PatternSearch (p :: ps) ts := hrec
            _ = i + PatternSearch (p :: ps) (t :: ts) := by
                  rw [hPS]
                  cases ts with
                  | nil =>
                      simp [PatternSearch, h]
                  | cons head tail =>
                      calc
                        i + 1 + (if (p :: ps).isPrefixOf (head :: tail) then 0
                            else PatternSearch (p :: ps) tail + 1)
                            = i + (PatternSearch (p :: ps) (head :: tail) + 1) := by
                                simpa [Nat.add_assoc, Nat.add_comm] using
                                  congrArg (fun n => i + n + 1) ((hPS (head :: tail)).symm)
                        _ = i + PatternSearch (p :: ps) (t :: head :: tail) := by
                              simpa [h, Nat.add_assoc, Nat.add_comm] using
                                congrArg (fun n => i + n) ((hPS (t :: head :: tail)).symm)
      · have hlt' := hlt (t :: ts) (Nat.not_le.mp hlen)
        have hlen' : ¬ ps.length ≤ ts.length := by simpa using hlen
        calc
          (naivePatternSearchFrom (p :: ps) (t :: ts) i).eval Comparison.natCost =
              ((pure (i + (t :: ts).length) : Prog (Comparison α) Nat)).eval
                Comparison.natCost := by
            rw [hdef]
            simp [hlen']
          _ = i + (t :: ts).length := by simp
          _ = i + PatternSearch (p :: ps) (t :: ts) := by simp [hlt']

theorem naivePatternSearch_eval [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).eval Comparison.natCost = PatternSearch pat txt := by
  simp [naivePatternSearch, naivePatternSearchFrom_eval]

end Correctness

section TimeComplexity

theorem prefixMatch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).time Comparison.natCost ≤ Nat.min pat.length txt.length := by
  induction pat generalizing txt with
  | nil => simp [prefixMatch]
  | cons p ps ih =>
    cases txt with
    | nil => simp [prefixMatch]
    | cons t ts =>
      by_cases h : p == t
      · have hih := ih ts
        simp [prefixMatch, h] at hih ⊢
        omega
      · simp [prefixMatch, h]

private lemma naivePatternSearchFrom_time_complexity_upper_bound [BEq α]
    (pat txt : List α) (i : Nat) :
    (naivePatternSearchFrom pat txt i).time Comparison.natCost ≤
      pat.length * (txt.length + 1 - pat.length) := by
  cases pat with
  | nil => simp [naivePatternSearchFrom]
  | cons p ps =>
    induction txt generalizing i with
    | nil => simp [naivePatternSearchFrom]
    | cons t ts ih =>
      have hdef :
          naivePatternSearchFrom (p :: ps) (t :: ts) i =
            if (p :: ps).length ≤ (t :: ts).length then
              (do
                let found ← prefixMatch (p :: ps) (t :: ts)
                if found then pure i else naivePatternSearchFrom (p :: ps) ts (i + 1))
            else
              pure (i + (t :: ts).length) := by
        rfl
      by_cases hlen : (p :: ps).length ≤ (t :: ts).length
      · have hpre :
            (prefixMatch (p :: ps) (t :: ts)).time Comparison.natCost ≤ (p :: ps).length :=
          (prefixMatch_time_complexity_upper_bound (p :: ps) (t :: ts)).trans (Nat.min_le_left _ _)
        have hlen' : ps.length ≤ ts.length := by simpa using hlen
        cases heval : (prefixMatch (p :: ps) (t :: ts)).eval Comparison.natCost with
        | false =>
            have hmult :
                (p :: ps).length * (ts.length + 1 - (p :: ps).length) + (p :: ps).length =
                  (p :: ps).length * ((t :: ts).length + 1 - (p :: ps).length) := by
              have hsub : (t :: ts).length + 1 - (p :: ps).length =
                  (ts.length + 1 - (p :: ps).length) + 1 := by
                simpa using (Nat.succ_sub hlen)
              rw [hsub, Nat.mul_succ]
            have hsum := Nat.add_le_add hpre (ih (i + 1))
            have hsum' :
                (prefixMatch (p :: ps) (t :: ts)).time Comparison.natCost +
                    (naivePatternSearchFrom (p :: ps) ts (i + 1)).time Comparison.natCost ≤
                  (p :: ps).length * (ts.length + 1 - (p :: ps).length) + (p :: ps).length := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
            rw [hdef]
            simpa [hlen', heval] using hsum'.trans_eq hmult
        | true =>
            have hone : 1 ≤ (t :: ts).length + 1 - (p :: ps).length := by
              have hsub : (t :: ts).length + 1 - (p :: ps).length =
                  (ts.length + 1 - (p :: ps).length) + 1 := by
                simpa using (Nat.succ_sub hlen)
              rw [hsub]
              simp
            have hmul : (p :: ps).length ≤
                (p :: ps).length * ((t :: ts).length + 1 - (p :: ps).length) :=
              Nat.le_mul_of_pos_right _ hone
            rw [hdef]
            simpa [hlen', heval] using hpre.trans hmul
      · have hlen' : ¬ ps.length ≤ ts.length := by simpa using hlen
        rw [hdef]
        simp [hlen']

theorem naivePatternSearch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).time Comparison.natCost ≤
      pat.length * (txt.length + 1 - pat.length) := by
  simpa [naivePatternSearch] using naivePatternSearchFrom_time_complexity_upper_bound pat txt 0

end TimeComplexity

end Algorithms

end Cslib
