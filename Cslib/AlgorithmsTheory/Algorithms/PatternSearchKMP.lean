/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.Models.Comparison
public import Cslib.AlgorithmsTheory.Algorithms.PatternSearchNaive
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Intervals
public import Mathlib.Data.List.Infix

@[expose] public section

/-!
# Knuth-Morris-Pratt pattern search

In this file we define the longest-proper-prefix / suffix table used by KMP, together
with the search procedure itself, in the `Comparison` query model.
-/

namespace Cslib

namespace Algorithms

open Prog

open Comparison

def innerLPSWhile (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length) :
    Prog (Comparison α) Int := do
  match fuel with
  | 0 =>
      return cnd
  | fuel + 1 =>
    if cnd < 0 then
      return cnd
    else do
      let cmp : Bool ← compare (pat[pos]'hpos) (pat[(Int.toNat cnd)]'hcndPat)
      if cmp then
        return cnd
      else do
        let nextCnd := table[(Int.toNat cnd)]'hcndTable
        have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat nextCnd < table.length := by omega
        innerLPSWhile fuel pos nextCnd pat table hpos hnextPat hnextTable htableLen htableBound

def LPSWhile (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length) :
    Prog (Comparison α) (List Int × Int) := do
  match fuel with
  | 0 =>
      return (table, cnd)
  | fuel + 1 =>
      let cmp : Bool ← compare (pat[pos]'hpos) (pat[(Int.toNat cnd)]'hcndPat)
      let fallbackCnd ←
        if cmp then
          pure cnd
        else
          let nextCnd := table[(Int.toNat cnd)]'hcndTable
          have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
          have hnextTable : Int.toNat nextCnd < table.length := by omega
          innerLPSWhile table.length pos nextCnd pat table
            hpos hnextPat hnextTable htableLen htableBound
      let entry : Int :=
        if cmp then
          table[(Int.toNat cnd)]'hcndTable
        else
          cnd
      let table' := table.set pos entry
      let nextCnd := fallbackCnd + 1
      have hposTable : pos < table.length := by omega
      have htableLen' : table'.length = pat.length + 1 := by
        simp only [List.length_set, htableLen, table']
      have hentryPat : Int.toNat entry < pat.length := by
        by_cases hcmp : cmp
        · simp only [hcmp, ↓reduceIte, entry]
          exact htableBound (Int.toNat cnd) hcndTable
        · simp only [hcmp, Bool.false_eq_true, ↓reduceIte, entry]
          exact hcndPat
      have htableBound' : ∀ (i : Nat) (hi : i < table'.length),
      Int.toNat (table'[i]'hi) < pat.length := by
        intro i hi
        by_cases hEq : i = pos
        · have hget : table'[i]? = some entry := by
            simpa only [table', hEq]
              using List.getElem?_set_eq_of_lt entry (l := table) (n := pos) hposTable
          have hget' : some (table'[i]'hi) = some entry := by
            rw [← List.getElem?_eq_getElem hi, hget]
          exact Option.some.inj hget' ▸ hentryPat
        · have hNe : pos ≠ i := fun h => hEq h.symm
          have hget : table'[i] = table[i]'(by simpa [table'] using hi) := by
            simpa only [table'] using List.getElem_set_of_ne hNe entry hi
          rw [hget]
          exact htableBound i (by simpa only [List.length_set, table'] using hi)
      if hnextPos : pos + 1 < pat.length then
        if hnextCndPat : Int.toNat nextCnd < pat.length then
          have hnextCndTable : Int.toNat nextCnd < table'.length := by omega
          LPSWhile fuel (pos + 1) nextCnd pat table'
            hnextPos hnextCndPat hnextCndTable htableLen' htableBound'
        else
          return (table', nextCnd)
      else
        return (table', nextCnd)

def buildLPS (pat : List α) : Prog (Comparison α) (List Int) := do
  match pat with
  | [] =>
      return [-1]
  | [_] =>
      return [-1, 0]
  | x :: y :: xs =>
      let table0 : List Int := -1 :: List.replicate (List.length (x :: y :: xs)) 0
      have hpos : 1 < (x :: y :: xs).length := by simp
      have hcndPat : Int.toNat (0 : Int) < (x :: y :: xs).length := by simp
      have hcndTable : Int.toNat (0 : Int) < table0.length := by simp [table0]
      have htableLen : table0.length = (x :: y :: xs).length + 1 := by simp [table0]
      have htableBound :
          ∀ (i : Nat) (hi : i < table0.length),
          Int.toNat (table0[i]'hi) < (x :: y :: xs).length := by
        intro i hi
        cases i <;> simp [table0]
      let (table, cnd) ←
        LPSWhile ((x :: y :: xs).length - 1) 1 0 (x :: y :: xs) table0
          hpos hcndPat hcndTable htableLen htableBound
      let table' := table.set (x :: y :: xs).length cnd
      return table'

/--
`kmpSearchFallback fuel t k pat table` follows KMP failure links from the current pattern
position `k` until either `pat[k]` matches the current text character `t` or the search
falls past the beginning of the pattern.

It returns `some k'` when `pat[k'] = t`, and `none` when the sentinel `-1` is reached.

The extra `fuel` argument ensures structural termination while traversing the failure links.
-/
def kmpSearchFallback
    (fuel : Nat) (t : α) (k : Nat) (pat : List α) (table : List Int) :
    Prog (Comparison α) (Option Nat) := do
  match fuel with
  | 0 =>
      return none
  | fuel + 1 =>
      match pat[k]? with
      | none =>
          return none
      | some pk =>
          let cmp : Bool ← compare pk t
          if cmp then
            return some k
          else
            match table[k]? with
            | none =>
                return none
            | some nextK =>
                if nextK < 0 then
                  return none
                else
                  kmpSearchFallback fuel t (Int.toNat nextK) pat table

/--
`kmpSearchPositionsAux txt j k pat table accRev` searches the remaining text `txt`, where `j`
is the current absolute text index, `k` is the current pattern position, and `accRev`
accumulates match positions in reverse order.
-/
def kmpSearchPositionsAux
    (txt : List α) (j k : Nat) (pat : List α) (table : List Int)
    (accRev : List Nat) :
    Prog (Comparison α) (List Nat) := do
  match txt with
  | [] =>
      return accRev.reverse
  | t :: ts =>
      let matched ← kmpSearchFallback table.length t k pat table
      match matched with
      | none =>
          kmpSearchPositionsAux ts (j + 1) 0 pat table accRev
      | some k' =>
          let nextK := k' + 1
          if nextK = pat.length then
            let start := j + 1 - pat.length
            let reset :=
              match table[pat.length]? with
              | some suffixLen =>
                  Int.toNat suffixLen
              | none =>
                  0
            kmpSearchPositionsAux ts (j + 1) reset pat table (start :: accRev)
          else
            kmpSearchPositionsAux ts (j + 1) nextK pat table accRev

/--
`kmpSearchPositions pat txt` returns all starting positions where `pat` occurs in `txt`.

For the empty pattern, this matches the library convention used by `PatternSearchAll`
and returns every position inside the text `0, 1, ..., txt.length - 1`.
-/
def kmpSearchPositions (pat txt : List α) : Prog (Comparison α) (List Nat) := do
  match pat with
  | [] =>
      return List.range txt.length
  | _ :: _ =>
      let table ← buildLPS pat
      kmpSearchPositionsAux txt 0 0 pat table []


private lemma initTable0_bound (pat : List α) (h : 0 < pat.length) :
    let table0 : List Int := -1 :: List.replicate pat.length 0
    (∀ (i : Nat) (hi : i < table0.length), Int.toNat (table0[i]'hi) < pat.length) ∧
    (∀ (i : Nat) (hi : i < table0.length), -1 ≤ table0[i]'hi) ∧
    (∀ (i : Nat) (hi : i < table0.length), Int.toNat (table0[i]'hi + 1) ≤ i) ∧
    table0.length = pat.length + 1 := by
  refine ⟨?_, ?_, ?_, by simp⟩ <;> (intro i hi; cases i <;> simp [h])

section TimeComplexity


private lemma int_toNat_add_one_eq {z : Int} (hz : 0 ≤ z) :
    Int.toNat (z + 1) = Int.toNat z + 1 := by
  apply Int.ofNat.inj
  simp
  omega

private lemma nextCnd_pat_table_bounds
    {pat : List α} {table : List Int} {cnd : Int}
    (hcndTable : Int.toNat cnd < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length) :
    let nextCnd := table[(Int.toNat cnd)]'hcndTable
    Int.toNat nextCnd < pat.length ∧ Int.toNat nextCnd < table.length := by
  exact ⟨htableBound _ hcndTable, by have := htableBound _ hcndTable; omega⟩

private lemma innerLPSWhile_time_eval_sum_zero_negOne [BEq α]
    (fuel pos : Nat) (pat : List α) (table : List Int)
    (hpos : pos < pat.length)
    (hnextPat : Int.toNat (-1 : Int) < pat.length)
    (hnextTable : Int.toNat (-1 : Int) < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length) :
    (innerLPSWhile fuel pos (-1) pat table
      hpos hnextPat hnextTable htableLen htableBound).time Comparison.natCost +
    Int.toNat ((innerLPSWhile fuel pos (-1) pat table
      hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost + 1) = 0 := by
  cases fuel <;> simp [innerLPSWhile, Prog.eval, Prog.time]

private lemma innerLPSWhile_eval_bounds [BEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length)
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi + 1) ≤ i)
    (hcndLower : -1 ≤ cnd) :
    (-1 ≤ (innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost) ∧
    ((innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).time Comparison.natCost +
      Int.toNat ((innerLPSWhile fuel pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost + 1)
        ≤ Int.toNat cnd + 2) := by
  induction fuel generalizing pos cnd with
  | zero =>
      constructor
      · simpa [innerLPSWhile, Prog.eval] using hcndLower
      · simp [innerLPSWhile, Prog.eval]
        omega
  | succ fuel ih =>
      by_cases hcndNeg : cnd < 0
      · have hcndEq : cnd = -1 := by omega
        subst hcndEq
        constructor
        · simp [innerLPSWhile, Prog.eval]
        · simp [innerLPSWhile, Prog.eval]
      · have hnextPat : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < pat.length :=
          htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < table.length := by omega
        have hnextLower : -1 ≤ table[(Int.toNat cnd)]'hcndTable :=
          htableLower (Int.toNat cnd) hcndTable
        by_cases hcmp : pat[pos]'hpos == pat[(Int.toNat cnd)]'hcndPat
        · constructor
          · simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using hcndLower
          · simp [innerLPSWhile, Prog.eval, hcndNeg, hcmp]
            omega
        · have hstep := htableStep (Int.toNat cnd) hcndTable
          by_cases hnextNeg : table[(Int.toNat cnd)]'hcndTable < 0
          · have hrecLower :=
              (ih pos (table[(Int.toNat cnd)]'hcndTable) hpos hnextPat hnextTable
                hnextLower).1
            have hnextEq : table[(Int.toNat cnd)]'hcndTable = -1 := by omega
            have hinnerZero :
                (innerLPSWhile fuel pos (table[(Int.toNat cnd)]'hcndTable) pat table
                  hpos hnextPat hnextTable htableLen htableBound).time
                  Comparison.natCost +
                Int.toNat
                  ((innerLPSWhile fuel pos (table[(Int.toNat cnd)]'hcndTable) pat table
                    hpos hnextPat hnextTable htableLen htableBound).eval
                    Comparison.natCost + 1) = 0 := by
              simpa [hnextEq] using
                innerLPSWhile_time_eval_sum_zero_negOne
                  fuel pos pat table hpos (by simpa [hnextEq] using hnextPat)
                  (by simpa [hnextEq] using hnextTable) htableLen htableBound
            constructor
            · simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using hrecLower
            · simp [innerLPSWhile, Prog.eval, Prog.time, hcndNeg, hcmp, hnextEq] at hinnerZero ⊢
              omega
          · have hnextNonneg : 0 ≤ table[(Int.toNat cnd)]'hcndTable := by omega
            have hstep' :
                Int.toNat (table[(Int.toNat cnd)]'hcndTable) + 1 ≤ Int.toNat cnd := by
              rw [← int_toNat_add_one_eq hnextNonneg]
              exact hstep
            have hrec :=
              ih pos (table[(Int.toNat cnd)]'hcndTable) hpos hnextPat hnextTable
                hnextLower
            constructor
            · simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using hrec.1
            · have hrecTime := hrec.2
              simp [Prog.eval] at hrecTime
              simp [innerLPSWhile, Prog.eval, hcndNeg, hcmp]
              omega

/-- Helper: `List.set` preserves table bounds. -/
private lemma table_set_bound {pat : List α} {table : List Int} {pos : Nat} {v : Int}
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length)
    (hv : Int.toNat v < pat.length) (hpos : pos < table.length)
    (i : Nat) (hi : i < (table.set pos v).length) :
    Int.toNat ((table.set pos v)[i]'hi) < pat.length := by
  simp only [List.length_set] at hi
  by_cases heq : i = pos
  · subst heq; simpa using hv
  · rw [List.getElem_set_of_ne (by omega)]; exact htableBound i (by omega)

/-- Helper: `List.set` preserves lower bounds. -/
private lemma table_set_lower {table : List Int} {pos : Nat} {v : Int}
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (hv : -1 ≤ v)
    (i : Nat) (hi : i < (table.set pos v).length) :
    -1 ≤ (table.set pos v)[i]'hi := by
  simp only [List.length_set] at hi
  by_cases heq : i = pos
  · subst heq; simpa using hv
  · rw [List.getElem_set_of_ne (by omega)]; exact htableLower i (by omega)

/-- Helper: `List.set` preserves the step invariant. -/
private lemma table_set_step {table : List Int} {pos : Nat} {v : Int}
    (htableStep : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi + 1) ≤ i)
    (hv : Int.toNat (v + 1) ≤ pos)
    (i : Nat) (hi : i < (table.set pos v).length) :
    Int.toNat ((table.set pos v)[i]'hi + 1) ≤ i := by
  simp only [List.length_set] at hi
  by_cases heq : i = pos
  · subst heq; simpa using hv
  · rw [List.getElem_set_of_ne (by omega)]; exact htableStep i (by omega)

private lemma LPSWhile_time_complexity_upper_bound [BEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length)
    (hcndNonneg : 0 ≤ cnd)
    (hcndStep : Int.toNat (cnd + 1) ≤ pos)
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi + 1) ≤ i) :
    (LPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).time
      Comparison.natCost ≤ 2 * fuel + Int.toNat cnd := by
  induction fuel generalizing pos cnd table hpos hcndPat hcndTable htableLen htableBound
    hcndNonneg hcndStep htableLower htableStep with
  | zero => simp [LPSWhile]
  | succ fuel ih =>
    unfold LPSWhile
    simp +zetaDelta only [FreeM.lift_def, FreeM.pure_eq_pure, FreeM.pure_bind',
      FreeM.bind_eq_bind, FreeM.liftBind_bind, FreeM.pure_bind, Prog.time_liftBind,
      Comparison.natCost_cost, Comparison.natCost_evalQuery]
    have hposTable : pos < table.length := by omega
    have hcndSucc := int_toNat_add_one_eq hcndNonneg
    have hcndLePos : Int.toNat cnd ≤ pos := by omega
    split_ifs with hcmp hpos' hcndPat'
    · -- cmp = true, pos + 1 < pat.length, nextCnd in range: recurse
      have hentryStep : Int.toNat (table[(Int.toNat cnd)]'hcndTable + 1) ≤ pos :=
        le_trans (htableStep (Int.toNat cnd) hcndTable) hcndLePos
      have hrec := ih (pos + 1) (cnd + 1) (table.set pos table[cnd.toNat]) hpos' hcndPat'
        (by simp only [List.length_set]; omega) (by rw [List.length_set, htableLen])
        (table_set_bound htableBound (htableBound _ hcndTable) hposTable)
        (by omega) (by rw [int_toNat_add_one_eq (by omega), hcndSucc]; omega)
        (table_set_lower htableLower (htableLower _ hcndTable))
        (table_set_step htableStep hentryStep)
      omega
    · simp [Prog.time_pure]
      omega
    · simp [Prog.time_pure]
      omega
    · -- cmp = false, pos + 1 < pat.length: inner loop + possible recurse
      rename_i hpos_next
      rw [Prog.time_bind]
      let nextCnd := table[(Int.toNat cnd)]'hcndTable
      have hnext := nextCnd_pat_table_bounds (pat := pat) (table := table)
        hcndTable htableLen htableBound
      have hnextPat : Int.toNat nextCnd < pat.length := by simpa [nextCnd] using hnext.1
      have hnextTable : Int.toNat nextCnd < table.length := by simpa [nextCnd] using hnext.2
      have hnextLower : -1 ≤ nextCnd := htableLower (Int.toNat cnd) hcndTable
      set inner : Prog (Comparison α) Int :=
        innerLPSWhile table.length pos nextCnd pat table
          hpos hnextPat hnextTable htableLen htableBound
      have hinnerLower := (innerLPSWhile_eval_bounds
        table.length pos nextCnd pat table
        hpos hnextPat hnextTable htableLen htableBound htableLower htableStep hnextLower).1
      have hnextNonneg : 0 ≤ inner.eval Comparison.natCost + 1 := by
        have : -1 ≤ inner.eval Comparison.natCost := by simpa [inner] using hinnerLower
        omega
      have hinner' :
          inner.time Comparison.natCost +
            Int.toNat (inner.eval Comparison.natCost + 1) ≤ Int.toNat cnd + 1 := by
        by_cases hnextNeg : nextCnd < 0
        · have hnextEq : nextCnd = -1 := by omega
          have : inner.time Comparison.natCost +
              Int.toNat (inner.eval Comparison.natCost + 1) = 0 := by
            simpa [inner, hnextEq] using innerLPSWhile_time_eval_sum_zero_negOne
              table.length pos pat table hpos (by simpa [hnextEq] using hnextPat)
              (by simpa [hnextEq] using hnextTable) htableLen htableBound
          omega
        · have hnextNonneg : 0 ≤ nextCnd := by omega
          have hstep' : Int.toNat nextCnd + 1 ≤ Int.toNat cnd := by
            rw [← int_toNat_add_one_eq hnextNonneg]
            simpa [nextCnd] using htableStep (Int.toNat cnd) hcndTable
          have : inner.time Comparison.natCost +
              Int.toNat (inner.eval Comparison.natCost + 1) ≤
                Int.toNat nextCnd + 2 := by
            simpa [inner] using (innerLPSWhile_eval_bounds
              table.length pos nextCnd pat table
              hpos hnextPat hnextTable htableLen htableBound htableLower htableStep hnextLower).2
          omega
      split_ifs with hcndPat_rec
      · have hnextStep : Int.toNat ((inner.eval Comparison.natCost + 1) + 1) ≤ pos + 1 := by
          rw [int_toNat_add_one_eq hnextNonneg]
          omega
        have hrec := ih (pos + 1) (inner.eval Comparison.natCost + 1)
          (table.set pos cnd) hpos_next hcndPat_rec
          (by simp only [List.length_set]; omega) (by rw [List.length_set, htableLen])
          (table_set_bound htableBound hcndPat hposTable) hnextNonneg hnextStep
          (table_set_lower htableLower (by omega))
          (table_set_step htableStep hcndStep)
        omega
      · rw [Prog.time_pure]
        simp
        omega
    · -- cmp = false, ¬(pos + 1 < pat.length)
      rw [Prog.time_bind, Prog.time_pure]
      let nextCnd := table[(Int.toNat cnd)]'hcndTable
      have hnext := nextCnd_pat_table_bounds (pat := pat) (table := table)
        hcndTable htableLen htableBound
      have hnextPat : Int.toNat nextCnd < pat.length := by simpa [nextCnd] using hnext.1
      have hnextTable : Int.toNat nextCnd < table.length := by simpa [nextCnd] using hnext.2
      have hnextLower : -1 ≤ nextCnd := htableLower (Int.toNat cnd) hcndTable
      set inner : Prog (Comparison α) Int :=
        innerLPSWhile table.length pos nextCnd pat table
          hpos hnextPat hnextTable htableLen htableBound
      have hinner :
          inner.time Comparison.natCost +
            Int.toNat (inner.eval Comparison.natCost + 1) ≤ Int.toNat cnd + 1 := by
        by_cases hnextNeg : nextCnd < 0
        · have hnextEq : nextCnd = -1 := by omega
          have : inner.time Comparison.natCost +
              Int.toNat (inner.eval Comparison.natCost + 1) = 0 := by
            simpa [inner, hnextEq] using innerLPSWhile_time_eval_sum_zero_negOne
              table.length pos pat table hpos (by simpa [hnextEq] using hnextPat)
              (by simpa [hnextEq] using hnextTable) htableLen htableBound
          omega
        · have hnextNonneg : 0 ≤ nextCnd := by omega
          have hstep' : Int.toNat nextCnd + 1 ≤ Int.toNat cnd := by
            rw [← int_toNat_add_one_eq hnextNonneg]
            simpa [nextCnd] using htableStep (Int.toNat cnd) hcndTable
          have : inner.time Comparison.natCost +
              Int.toNat (inner.eval Comparison.natCost + 1) ≤
                Int.toNat nextCnd + 2 := by
            simpa [inner] using (innerLPSWhile_eval_bounds
              table.length pos nextCnd pat table
              hpos hnextPat hnextTable htableLen htableBound htableLower htableStep hnextLower).2
          omega
      simp [inner, nextCnd] at hinner ⊢
      omega

theorem buildLPS_time_complexity_upper_bound [BEq α]
    (pat : List α) :
    (buildLPS pat).time Comparison.natCost ≤
      2 * (pat.length - 1) := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [buildLPS]
      | cons y xs =>
          let pat' := x :: y :: xs
          let table0 : List Int := -1 :: List.replicate pat'.length 0
          rcases initTable0_bound pat' (by simp [pat']) with
            ⟨htableBound, htableLower, htableStep, _⟩
          simpa [buildLPS, pat', table0] using
            LPSWhile_time_complexity_upper_bound (pat'.length - 1) 1 0 pat' table0
              (by simp [pat']) (by simp [pat']) (by simp [pat', table0])
              (by simp [pat', table0]) htableBound (by omega) (by simp)
              htableLower htableStep

end TimeComplexity

section Correctness

theorem kmpSearchPositions_eval_nil [BEq α] (txt : List α) :
    (kmpSearchPositions ([] : List α) txt).eval Comparison.natCost =
      PatternSearchAll ([] : List α) txt := by
  simp [kmpSearchPositions, PatternSearchAll]

private def Border (pat : List α) (n l : Nat) : Prop :=
  l < n ∧ pat.take l = (pat.take n).drop (n - l)

private def LongestBorder (pat : List α) (n l : Nat) : Prop :=
  Border pat n l ∧ ∀ l', Border pat n l' → l' ≤ l

private def FailureEntry [BEq α] (pat : List α) (k : Nat) (hk : k < pat.length) (v : Int) : Prop :=
  if _hneg : v < 0 then
    ∀ l, (hl : Border pat k l) → pat[k]'hk = pat[l]'(lt_trans hl.1 hk)
  else
    let n := Int.toNat v
    ∃ hn : Border pat k n,
      pat[k]'hk ≠ pat[n]'(lt_trans hn.1 hk) ∧
      ∀ l, (hl : Border pat k l) →
        pat[k]'hk ≠ pat[l]'(lt_trans hl.1 hk) → l ≤ n

private def BestMatchingBorder [BEq α] (pat : List α) (n : Nat) (hn : n < pat.length)
    (l : Nat) : Prop :=
  ∃ hl : Border pat n l,
    pat[n]'hn = pat[l]'(lt_trans hl.1 hn) ∧
    ∀ l', (hl' : Border pat n l') →
      pat[n]'hn = pat[l']'(lt_trans hl'.1 hn) → l' ≤ l

private def FailurePrefix [BEq α] (pat : List α) (table : List Int) (pos : Nat)
    (hpos : pos ≤ pat.length) (htableLen : table.length = pat.length + 1) : Prop :=
  ∀ i, (hi : i < pos) →
    FailureEntry pat i (by omega) (table[i]'(by omega))

private def MatchingFrontier (pat : List α) (n : Nat) (hn : n < pat.length) (l : Nat) : Prop :=
  Border pat n l ∧
    ∀ l', (hl' : Border pat n l') →
      pat[n]'hn = pat[l']'(lt_trans hl'.1 hn) → l' ≤ l

private lemma border_zero {pat : List α} {n : Nat} (hn : 0 < n) : Border pat n 0 :=
  ⟨hn, by simp⟩

private lemma border_trans {pat : List α} {n c l : Nat}
    (hcn : Border pat n c) (hlc : Border pat c l) : Border pat n l := by
  rcases hcn with ⟨hclt, hcn⟩; rcases hlc with ⟨hllt, hlc⟩
  exact ⟨by omega, by rw [hlc, hcn, List.drop_drop]; congr 1; omega⟩

private lemma border_of_longest_prefix {pat : List α} {n c l : Nat}
    (hcn : Border pat n c) (hl : Border pat n l) (hlt : l < c) : Border pat c l := by
  exact ⟨hlt, by rw [hcn.2, List.drop_drop]; convert hl.2 using 2; have := hcn.1; omega⟩

private lemma border_extend [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hborder : Border pat n l) (hcmp : pat[n]'hn = pat[l]'hl) :
    Border pat (n + 1) (l + 1) := by
  rcases hborder with ⟨hlt, hborder⟩
  constructor
  · omega
  · rw [show (n + 1) - (l + 1) = n - l by omega]
    rw [← List.take_concat_get' pat l hl, ← List.take_concat_get' pat n hn]
    have htakeLen : (pat.take n).length = n := by simp [hn.le]
    rw [List.drop_append, htakeLen]
    have hsub : n - l - n = 0 := by omega
    simp [hsub, hborder, hcmp]

private lemma border_prev [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hborder : Border pat (n + 1) (l + 1)) :
    Border pat n l ∧ pat[n]'hn = pat[l]'hl := by
  rcases hborder with ⟨hlt, hborder0⟩
  have hborder : pat.take (l + 1) = (pat.take (n + 1)).drop (n - l) := by
    rwa [show n + 1 - (l + 1) = n - l by omega] at hborder0
  have htakeLen : (pat.take n).length = n := by simp [hn.le]
  have hdrop : (pat.take (n + 1)).drop (n - l) = (pat.take n).drop (n - l) ++ [pat[n]'hn] := by
    rw [← List.take_concat_get' pat n hn, List.drop_append, htakeLen]
    have hsub : n - l - n = 0 := by omega
    simp [hsub]
  have hleft : pat.take (l + 1) = pat.take l ++ [pat[l]'hl] := by
    symm
    exact List.take_concat_get' pat l hl
  rw [hleft, hdrop] at hborder
  have hlenEq : (pat.take l).length = ((pat.take n).drop (n - l)).length := by
    simp [htakeLen]
    omega
  have hpair := List.append_inj hborder hlenEq
  constructor
  · constructor
    · omega
    · exact hpair.1
  · simpa using hpair.2.symm

private lemma longestBorder_extend [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hlong : LongestBorder pat n l)
    (hcmp : pat[n]'hn = pat[l]'hl) :
    LongestBorder pat (n + 1) (l + 1) := by
  rcases hlong with ⟨hlBorder, hlMax⟩
  refine ⟨border_extend hn hl hlBorder hcmp, fun l' hl' => ?_⟩
  cases l' with
  | zero => omega
  | succ l'' =>
    have hprev := border_prev hn (show l'' < pat.length by have := hl'.1; omega) hl'
    exact Nat.succ_le_succ (hlMax l'' hprev.1)

private lemma bestMatchingBorder_to_longest [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hbest : BestMatchingBorder pat n hn l) :
    LongestBorder pat (n + 1) (l + 1) := by
  rcases hbest with ⟨hlBorder, hcmp, hlMax⟩
  refine ⟨border_extend hn hl hlBorder hcmp, fun l' hl' => ?_⟩
  cases l' with
  | zero => omega
  | succ l'' =>
    have hprev := border_prev hn (show l'' < pat.length by have := hl'.1; omega) hl'
    exact Nat.succ_le_succ (hlMax l'' hprev.1 hprev.2)

private lemma no_matching_border_to_longest_zero [BEq α] {pat : List α} {n : Nat}
    (hn : n < pat.length)
    (hnone : ∀ l, (hl : Border pat n l) →
      pat[n]'hn ≠ pat[l]'(lt_trans hl.1 hn)) :
    LongestBorder pat (n + 1) 0 := by
  refine ⟨border_zero (Nat.succ_pos _), fun l' hl' => ?_⟩
  cases l' with
  | zero => omega
  | succ l'' =>
    have hprev := border_prev hn (show l'' < pat.length by have := hl'.1; omega) hl'
    exact absurd hprev.2 (hnone l'' hprev.1)

private lemma failure_transfer_of_eq [BEq α] {pat : List α} {pos c : Nat} {v : Int}
    (hpos : pos < pat.length) (hc : c < pat.length)
    (hlong : LongestBorder pat pos c)
    (hv : FailureEntry pat c hc v)
    (hcmp : pat[pos]'hpos = pat[c]'hc) :
    FailureEntry pat pos hpos v := by
  rcases hlong with ⟨hcBorder, hcMax⟩
  unfold FailureEntry at hv ⊢
  by_cases hneg : v < 0
  · rw [dif_pos hneg] at hv ⊢
    intro l hl
    by_cases hlc : l = c
    · simpa [hlc] using hcmp
    · have hle : l ≤ c := hcMax l hl
      have hlt : l < c := by omega
      have hlBorderC : Border pat c l := border_of_longest_prefix hcBorder hl hlt
      have hEq : pat[c]'hc = pat[l]'(lt_trans hlBorderC.1 hc) := hv l hlBorderC
      simpa [hcmp] using hEq
  · rw [dif_neg hneg] at hv ⊢
    rcases hv with ⟨hnBorder, hvNe, hvMax⟩
    refine ⟨border_trans hcBorder hnBorder, ?_, ?_⟩
    · intro hEq
      apply hvNe
      simpa [hcmp] using hEq
    · intro l hl hne
      by_cases hlc : l = c
      · subst hlc
        exfalso
        exact hne hcmp
      · have hle : l ≤ c := hcMax l hl
        have hlt : l < c := by omega
        have hlBorderC : Border pat c l := border_of_longest_prefix hcBorder hl hlt
        have hne' : pat[c]'hc ≠ pat[l]'(lt_trans hlBorderC.1 hc) := by
          intro hEq
          apply hne
          simpa [hcmp] using hEq
        exact hvMax l hlBorderC hne'

private lemma failure_of_longest_mismatch [BEq α] {pat : List α} {pos c : Nat}
    (hpos : pos < pat.length) (hc : c < pat.length)
    (hlong : LongestBorder pat pos c)
    (hcmp : pat[pos]'hpos ≠ pat[c]'hc) :
    FailureEntry pat pos hpos c := by
  rcases hlong with ⟨hcBorder, hcMax⟩
  have hnonneg : ¬ ((c : Int) < 0) := by simp
  unfold FailureEntry
  rw [dif_neg hnonneg]
  change
    ∃ hn : Border pat pos c,
      pat[pos]'hpos ≠ pat[c]'hc ∧
      ∀ l, (hl : Border pat pos l) → pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos) → l ≤ c
  refine ⟨hcBorder, hcmp, ?_⟩
  intro l hl _
  exact hcMax l hl

private lemma failureEntry_zero [BEq α] {pat : List α} (h0 : 0 < pat.length) :
    FailureEntry pat 0 h0 (-1) := by
  unfold FailureEntry
  rw [dif_pos (by decide : (-1 : Int) < 0)]
  intro l hl
  exact absurd hl.1 (Nat.not_lt_zero _)

private lemma failureEntry_target_lt [BEq α] {pat : List α} {k : Nat} {hk : k < pat.length}
    {v : Int} (hv : FailureEntry pat k hk v) (hnonneg : 0 ≤ v) :
    Int.toNat v < k := by
  have hneg : ¬ v < 0 := by omega
  have hv' :
      ∃ hn : Border pat k (Int.toNat v),
        pat[k]'hk ≠ pat[Int.toNat v]'(lt_trans hn.1 hk) ∧
        ∀ l, (hl : Border pat k l) →
          pat[k]'hk ≠ pat[l]'(lt_trans hl.1 hk) → l ≤ Int.toNat v := by
    simpa [FailureEntry, hneg] using hv
  rcases hv' with ⟨hnBorder, _, _⟩
  exact hnBorder.1

private lemma longestBorder_one {pat : List α} :
    LongestBorder pat 1 0 :=
  ⟨border_zero (Nat.succ_pos _), fun _ hl => Nat.le_of_lt_succ hl.1⟩

private lemma longestBorder_to_matchingFrontier {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hlong : LongestBorder pat n l) :
    MatchingFrontier pat n hn l :=
  ⟨hlong.1, fun l' hl' _ => hlong.2 l' hl'⟩

private lemma matchingFrontier_to_best [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hfront : MatchingFrontier pat n hn l)
    (hcmp : pat[n]'hn = pat[l]'hl) :
    BestMatchingBorder pat n hn l :=
  ⟨hfront.1, by simpa using hcmp, hfront.2⟩

private lemma no_matching_of_failure_neg [BEq α] {pat : List α} {pos c : Nat} {v : Int}
    (hpos : pos < pat.length)
    (hfront : MatchingFrontier pat pos hpos c)
    (hc : c < pat.length)
    (hv : FailureEntry pat c hc v)
    (hneg : v < 0)
    (hmis : pat[pos]'hpos ≠ pat[c]'hc) :
    ∀ l, (hl : Border pat pos l) →
      pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos) := by
  rcases hfront with ⟨hcBorder, hcMax⟩
  have hv' : ∀ l, (hl : Border pat c l) → pat[c]'hc = pat[l]'(lt_trans hl.1 hc) := by
    simpa [FailureEntry, hneg] using hv
  intro l hl hEq
  by_cases hlc : l = c
  · subst hlc
    exact hmis (by simpa using hEq)
  · have hle : l ≤ c := hcMax l hl hEq
    have hlt : l < c := by omega
    have hlBorderC : Border pat c l := border_of_longest_prefix hcBorder hl hlt
    have hEqC : pat[c]'hc = pat[l]'(lt_trans hlBorderC.1 hc) := hv' l hlBorderC
    exact hmis (by simpa using hEq.trans hEqC.symm)

private lemma matchingFrontier_of_failure_pos [BEq α] {pat : List α} {pos c : Nat} {v : Int}
    (hpos : pos < pat.length)
    (hfront : MatchingFrontier pat pos hpos c)
    (hc : c < pat.length)
    (hv : FailureEntry pat c hc v)
    (hnonneg : 0 ≤ v)
    (hmis : pat[pos]'hpos ≠ pat[c]'hc) :
    MatchingFrontier pat pos hpos (Int.toNat v) := by
  rcases hfront with ⟨hcBorder, hcMax⟩
  have hneg : ¬ v < 0 := by omega
  have hv' :
      ∃ hn : Border pat c (Int.toNat v),
        pat[c]'hc ≠ pat[Int.toNat v]'(lt_trans hn.1 hc) ∧
        ∀ l, (hl : Border pat c l) →
          pat[c]'hc ≠ pat[l]'(lt_trans hl.1 hc) → l ≤ Int.toNat v := by
    simpa [FailureEntry, hneg] using hv
  rcases hv' with ⟨hnBorder, hvNe, hvMax⟩
  refine ⟨border_trans hcBorder hnBorder, ?_⟩
  intro l hl hEq
  by_cases hlc : l = c
  · subst hlc
    exfalso
    exact hmis (by simpa using hEq)
  · have hle : l ≤ c := hcMax l hl hEq
    have hlt : l < c := by omega
    have hlBorderC : Border pat c l := border_of_longest_prefix hcBorder hl hlt
    have hne : pat[c]'hc ≠ pat[l]'(lt_trans hlBorderC.1 hc) := by
      intro hEqC
      apply hmis
      simpa using hEq.trans hEqC.symm
    exact hvMax l hlBorderC hne

private lemma initial_failurePrefix [BEq α] {pat : List α} (h0 : 0 < pat.length) :
    FailurePrefix pat (-1 :: List.replicate pat.length 0) 1 (by omega)
      (show (-1 :: List.replicate pat.length 0 : List Int).length = pat.length + 1 by simp) := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  have hidx : 0 < (-1 :: List.replicate pat.length 0 : List Int).length := by
    simp [h0]
  simpa using
    (failureEntry_zero h0 :
      FailureEntry pat 0 h0 ((-1 :: List.replicate pat.length 0)[0]'hidx))

private lemma innerLPSWhile_eval_frontier [BEq α] [LawfulBEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (hcndFuel : Int.toNat cnd < fuel)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length)
    (hentries : FailurePrefix pat table pos hpos.le htableLen)
    (hcndNonneg : 0 ≤ cnd)
    (hfront : MatchingFrontier pat pos hpos (Int.toNat cnd)) :
    let r := (innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost
    (r < 0 → ∀ l, (hl : Border pat pos l) →
      pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
    (0 ≤ r → BestMatchingBorder pat pos hpos (Int.toNat r)) := by
  induction fuel generalizing cnd with
  | zero =>
      omega
  | succ fuel ih =>
      have hcndNeg : ¬ cnd < 0 := by omega
      have hcndPos : Int.toNat cnd < pos := hfront.1.1
      have hv : FailureEntry pat (Int.toNat cnd) hcndPat
          (table[Int.toNat cnd]'hcndTable) := by
        simpa [FailurePrefix] using hentries (Int.toNat cnd) hcndPos
      by_cases hcmp : pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat
      · have hEq : pat[pos]'hpos = pat[Int.toNat cnd]'hcndPat := by
          simpa using hcmp
        have hbest : BestMatchingBorder pat pos hpos (Int.toNat cnd) :=
          matchingFrontier_to_best hpos hcndPat hfront hEq
        have hbranch :
            (cnd < 0 → ∀ l, (hl : Border pat pos l) →
              pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
            (0 ≤ cnd → BestMatchingBorder pat pos hpos (Int.toNat cnd)) := by
          constructor
          · intro hr
            omega
          · intro _
            exact hbest
        simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using hbranch
      · have hMis : pat[pos]'hpos ≠ pat[Int.toNat cnd]'hcndPat := by
          intro hEq
          exact hcmp (by simp [hEq])
        set nextCnd : Int := table[Int.toNat cnd]'hcndTable with hnextEq
        have hnext := nextCnd_pat_table_bounds (pat := pat) (table := table)
          hcndTable htableLen htableBound
        have hnextPat : Int.toNat nextCnd < pat.length := by
          simpa [hnextEq] using hnext.1
        have hnextTable : Int.toNat nextCnd < table.length := by
          simpa [hnextEq] using hnext.2
        by_cases hnextNeg : nextCnd < 0
        · have hinnerNeg :
              (innerLPSWhile fuel pos nextCnd pat table
                hpos hnextPat hnextTable htableLen htableBound).eval
                  Comparison.natCost = nextCnd := by
            cases fuel <;> simp [innerLPSWhile, Prog.eval, hnextNeg]
          have hbranch :
              (nextCnd < 0 → ∀ l, (hl : Border pat pos l) →
                pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
              (0 ≤ nextCnd → BestMatchingBorder pat pos hpos (Int.toNat nextCnd)) := by
            constructor
            · intro _
              exact no_matching_of_failure_neg hpos hfront hcndPat (by simpa [hnextEq] using hv)
                hnextNeg hMis
            · intro hr
              omega
          have hrecBranch :
              let r := (innerLPSWhile fuel pos nextCnd pat table
                hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost
              (r < 0 → ∀ l, (hl : Border pat pos l) →
                pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
              (0 ≤ r → BestMatchingBorder pat pos hpos (Int.toNat r)) := by
            simpa [hinnerNeg] using hbranch
          simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp, hnextEq] using hrecBranch
        · have hnextNonneg : 0 ≤ nextCnd := by omega
          have hnextFuel : Int.toNat nextCnd < fuel := by
            have hlt : Int.toNat nextCnd < Int.toNat cnd := by
              simpa [hnextEq] using failureEntry_target_lt hv hnextNonneg
            omega
          have hfront' : MatchingFrontier pat pos hpos (Int.toNat nextCnd) :=
            matchingFrontier_of_failure_pos hpos hfront hcndPat
              (by simpa [hnextEq] using hv) hnextNonneg hMis
          simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp, hnextEq] using
            ih nextCnd hnextPat hnextTable hnextFuel hnextNonneg hfront'

private def LPSInvariant [BEq α] (pat : List α) (pos : Nat) (cnd : Int) (table : List Int)
    (hpos : pos < pat.length) (_hcndPat : Int.toNat cnd < pat.length)
    (htableLen : table.length = pat.length + 1) : Prop :=
  0 ≤ cnd ∧ FailurePrefix pat table pos hpos.le htableLen ∧
    LongestBorder pat pos (Int.toNat cnd)

private def lpsStepEntry [BEq α]
    (pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) : Int :=
  if pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat then
    table[Int.toNat cnd]'hcndTable
  else
    cnd

private def lpsStepFallback [BEq α]
    (pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length) :
    Int :=
  if hcmp : pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat then
    cnd
  else
    let nextCnd := table[Int.toNat cnd]'hcndTable
    have hnext := nextCnd_pat_table_bounds (pat := pat) (table := table)
      hcndTable htableLen htableBound
    have hnextPat : Int.toNat nextCnd < pat.length := by
      simpa [nextCnd] using hnext.1
    have hnextTable : Int.toNat nextCnd < table.length := by
      simpa [nextCnd] using hnext.2
    (innerLPSWhile table.length pos nextCnd pat table
      hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost

private lemma failurePrefix_set [BEq α] {pat : List α} {table : List Int} {pos : Nat} {entry : Int}
    (hpos : pos < pat.length) (htableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pos hpos.le htableLen)
    (hentry : FailureEntry pat pos hpos entry) :
    ∃ hlen : (table.set pos entry).length = pat.length + 1,
      FailurePrefix pat (table.set pos entry) (pos + 1) (by omega) hlen := by
  refine ⟨by simpa [List.length_set] using htableLen, ?_⟩
  intro i hi
  by_cases heq : i = pos
  · subst heq
    simpa only [List.getElem_set_self] using hentry
  · have hiPos : i < pos := by omega
    have hj : i < (table.set pos entry).length := by
      simpa [List.length_set, htableLen] using (show i < pat.length + 1 by omega)
    have hget :
        (table.set pos entry)[i]'hj =
          table[i]'(by simpa [List.length_set, htableLen] using hj) := by
      simpa using List.getElem_set_of_ne (l := table) (i := pos) (j := i) (h := by omega) entry hj
    have hfp :
        FailureEntry pat i (by omega)
          (table[i]'(by simpa [List.length_set, htableLen] using hj)) := by
      simpa using hprefix i hiPos
    simpa [hget] using hfp

private lemma lpsStep_invariant [BEq α] [LawfulBEq α]
    (pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length)
    (hcndNonneg : 0 ≤ cnd) (hcndStep : Int.toNat (cnd + 1) ≤ pos)
    (hprefix : FailurePrefix pat table pos hpos.le htableLen)
    (hlong : LongestBorder pat pos (Int.toNat cnd))
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi + 1) ≤ i) :
    let entry := lpsStepEntry pos cnd pat table hpos hcndPat hcndTable
    let table' := table.set pos entry
    let nextCnd :=
      lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound + 1
    ∃ hlen : table'.length = pat.length + 1,
      FailurePrefix pat table' (pos + 1) (by omega) hlen ∧
      (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi) < pat.length) ∧
      (∀ (i : Nat) (hi : i < table'.length), -1 ≤ table'[i]'hi) ∧
      (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi + 1) ≤ i) ∧
      0 ≤ nextCnd ∧
      LongestBorder pat (pos + 1) (Int.toNat nextCnd) := by
  dsimp [lpsStepEntry, lpsStepFallback]
  have hposTable : pos < table.length := by
    calc
      pos < pat.length := hpos
      _ < pat.length + 1 := Nat.lt_succ_self _
      _ = table.length := htableLen.symm
  have hcndPos : Int.toNat cnd < pos := hlong.1.1
  have hcndLePos : Int.toNat cnd ≤ pos := by omega
  have hfront : MatchingFrontier pat pos hpos (Int.toNat cnd) :=
    longestBorder_to_matchingFrontier hpos hlong
  have hvCur : FailureEntry pat (Int.toNat cnd) hcndPat (table[Int.toNat cnd]'hcndTable) := by
    simpa [FailurePrefix] using hprefix (Int.toNat cnd) hcndPos
  by_cases hcmp : pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat
  · have hEq : pat[pos]'hpos = pat[Int.toNat cnd]'hcndPat := by
      simpa using hcmp
    have hentry :
        FailureEntry pat pos hpos (table[Int.toNat cnd]'hcndTable) :=
      failure_transfer_of_eq hpos hcndPat hlong hvCur hEq
    rcases failurePrefix_set hpos htableLen hprefix hentry with ⟨hlen, hprefix'⟩
    have hentryStep : Int.toNat (table[Int.toNat cnd]'hcndTable + 1) ≤ pos :=
      le_trans (htableStep (Int.toNat cnd) hcndTable) hcndLePos
    have hlong' : LongestBorder pat (pos + 1) (Int.toNat (cnd + 1)) := by
      simpa [int_toNat_add_one_eq hcndNonneg] using
        (longestBorder_extend hpos hcndPat hlong hEq)
    have hres :
        ∃ hlen : (table.set pos (table[Int.toNat cnd]'hcndTable)).length = pat.length + 1,
          FailurePrefix pat (table.set pos (table[Int.toNat cnd]'hcndTable))
            (pos + 1) (by omega) hlen ∧
          (∀ (i : Nat) (hi : i < (table.set pos (table[Int.toNat cnd]'hcndTable)).length),
            Int.toNat ((table.set pos (table[Int.toNat cnd]'hcndTable))[i]'hi) < pat.length) ∧
          (∀ (i : Nat) (hi : i < (table.set pos (table[Int.toNat cnd]'hcndTable)).length),
            -1 ≤ (table.set pos (table[Int.toNat cnd]'hcndTable))[i]'hi) ∧
          (∀ (i : Nat) (hi : i < (table.set pos (table[Int.toNat cnd]'hcndTable)).length),
            Int.toNat ((table.set pos (table[Int.toNat cnd]'hcndTable))[i]'hi + 1) ≤ i) ∧
          0 ≤ cnd + 1 ∧
          LongestBorder pat (pos + 1) (Int.toNat (cnd + 1)) := by
      refine ⟨hlen, hprefix', ?_, ?_, ?_, ?_, hlong'⟩
      · exact table_set_bound htableBound (htableBound _ hcndTable) hposTable
      · exact table_set_lower htableLower (htableLower _ hcndTable)
      · exact table_set_step htableStep hentryStep
      · omega
    simpa [hcmp] using hres
  · have hMis : pat[pos]'hpos ≠ pat[Int.toNat cnd]'hcndPat := by
      intro hEq
      exact hcmp (by simp [hEq])
    have hentry :
        FailureEntry pat pos hpos cnd := by
      simpa [show ((Int.toNat cnd : Nat) : Int) = cnd by omega] using
        (failure_of_longest_mismatch hpos hcndPat hlong hMis :
          FailureEntry pat pos hpos (Int.toNat cnd))
    rcases failurePrefix_set hpos htableLen hprefix hentry with ⟨hlen, hprefix'⟩
    let prev : Int := table[Int.toNat cnd]'hcndTable
    have hprevPat : Int.toNat prev < pat.length := by
      simpa [prev] using htableBound (Int.toNat cnd) hcndTable
    have hprevTable : Int.toNat prev < table.length := by
      calc
        Int.toNat prev < pat.length := hprevPat
        _ < pat.length + 1 := Nat.lt_succ_self _
        _ = table.length := htableLen.symm
    have hprevLower : -1 ≤ prev := by
      simpa [prev] using htableLower (Int.toNat cnd) hcndTable
    have hbound' :
        ∀ (i : Nat) (hi : i < (table.set pos cnd).length),
          Int.toNat ((table.set pos cnd)[i]'hi) < pat.length :=
      table_set_bound htableBound hcndPat hposTable
    have hlower' :
        ∀ (i : Nat) (hi : i < (table.set pos cnd).length),
          -1 ≤ (table.set pos cnd)[i]'hi :=
      table_set_lower htableLower (by omega)
    have hstep' :
        ∀ (i : Nat) (hi : i < (table.set pos cnd).length),
          Int.toNat ((table.set pos cnd)[i]'hi + 1) ≤ i :=
      table_set_step htableStep hcndStep
    let fallback : Int :=
      (innerLPSWhile table.length pos prev pat table
        hpos hprevPat hprevTable htableLen htableBound).eval Comparison.natCost
    by_cases hprevNeg : prev < 0
    · have hprevEq : prev = -1 := by omega
      have hnoMatch : ∀ l, (hl : Border pat pos l) →
          pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos) :=
        no_matching_of_failure_neg hpos hfront hcndPat hvCur hprevNeg hMis
      have htablePos : 0 < table.length := by omega
      have hfallbackEq : fallback = prev := by
        subst fallback
        cases hlenTable : table.length with
        | zero =>
            omega
        | succ n =>
            simp [innerLPSWhile, Prog.eval, hprevNeg]
      have hnextNonneg : 0 ≤ fallback + 1 := by omega
      have hlong' : LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
        simpa [hfallbackEq, hprevEq] using no_matching_border_to_longest_zero hpos hnoMatch
      have hres :
          ∃ hlen : (table.set pos cnd).length = pat.length + 1,
            FailurePrefix pat (table.set pos cnd) (pos + 1) (by omega) hlen ∧
            (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
              Int.toNat ((table.set pos cnd)[i]'hi) < pat.length) ∧
            (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
              -1 ≤ (table.set pos cnd)[i]'hi) ∧
            (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
              Int.toNat ((table.set pos cnd)[i]'hi + 1) ≤ i) ∧
            0 ≤ fallback + 1 ∧
            LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
        refine ⟨hlen, hprefix', hbound', hlower', hstep', hnextNonneg, hlong'⟩
      simpa [hcmp, prev, fallback] using hres
    · have hprevNonneg : 0 ≤ prev := by omega
      have hfrontPrev : MatchingFrontier pat pos hpos (Int.toNat prev) :=
        matchingFrontier_of_failure_pos hpos hfront hcndPat hvCur hprevNonneg hMis
      have hinner :
          let r := (innerLPSWhile table.length pos prev pat table
            hpos hprevPat hprevTable htableLen htableBound).eval Comparison.natCost
          (r < 0 → ∀ l, (hl : Border pat pos l) →
            pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
          (0 ≤ r → BestMatchingBorder pat pos hpos (Int.toNat r)) :=
        innerLPSWhile_eval_frontier
          table.length pos prev pat table hpos hprevPat hprevTable hprevTable
          htableLen htableBound hprefix hprevNonneg hfrontPrev
      have hfallbackLower : -1 ≤ fallback := by
        simpa [fallback] using (innerLPSWhile_eval_bounds
          table.length pos prev pat table
          hpos hprevPat hprevTable htableLen htableBound htableLower htableStep hprevLower).1
      by_cases hfallbackNeg : fallback < 0
      · have hfallbackEq : fallback = -1 := by omega
        have hnoMatch : ∀ l, (hl : Border pat pos l) →
            pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos) := by
          simpa [fallback] using hinner.1 hfallbackNeg
        have hnextNonneg : 0 ≤ fallback + 1 := by omega
        have hlong' : LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
          simpa [hfallbackEq] using no_matching_border_to_longest_zero hpos hnoMatch
        have hres :
            ∃ hlen : (table.set pos cnd).length = pat.length + 1,
              FailurePrefix pat (table.set pos cnd) (pos + 1) (by omega) hlen ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                Int.toNat ((table.set pos cnd)[i]'hi) < pat.length) ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                -1 ≤ (table.set pos cnd)[i]'hi) ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                Int.toNat ((table.set pos cnd)[i]'hi + 1) ≤ i) ∧
              0 ≤ fallback + 1 ∧
              LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
          refine ⟨hlen, hprefix', hbound', hlower', hstep', hnextNonneg, hlong'⟩
        simpa [hcmp, prev, fallback] using hres
      · have hfallbackNonneg : 0 ≤ fallback := by omega
        have hbest : BestMatchingBorder pat pos hpos (Int.toNat fallback) := by
          simpa [fallback] using hinner.2 hfallbackNonneg
        rcases hbest with ⟨hl, hbestEq, hbestMax⟩
        have hfallbackPat : Int.toNat fallback < pat.length := lt_trans hl.1 hpos
        have hbest' : BestMatchingBorder pat pos hpos (Int.toNat fallback) :=
          ⟨hl, hbestEq, hbestMax⟩
        have hnextNonneg : 0 ≤ fallback + 1 := by omega
        have hlong' : LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
          simpa [int_toNat_add_one_eq hfallbackNonneg] using
            (bestMatchingBorder_to_longest hpos hfallbackPat hbest')
        have hres :
            ∃ hlen : (table.set pos cnd).length = pat.length + 1,
              FailurePrefix pat (table.set pos cnd) (pos + 1) (by omega) hlen ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                Int.toNat ((table.set pos cnd)[i]'hi) < pat.length) ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                -1 ≤ (table.set pos cnd)[i]'hi) ∧
              (∀ (i : Nat) (hi : i < (table.set pos cnd).length),
                Int.toNat ((table.set pos cnd)[i]'hi + 1) ≤ i) ∧
              0 ≤ fallback + 1 ∧
              LongestBorder pat (pos + 1) (Int.toNat (fallback + 1)) := by
          refine ⟨hlen, hprefix', hbound', hlower', hstep', hnextNonneg, hlong'⟩
        simpa [hcmp, prev, fallback] using hres

private lemma LPSWhile_eval_invariant [BEq α] [LawfulBEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length)
    (hfuel : fuel + pos = pat.length)
    (hinv : LPSInvariant pat pos cnd table hpos hcndPat htableLen)
    (hcndStep : Int.toNat (cnd + 1) ≤ pos)
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi + 1) ≤ i) :
    let out := (LPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost
    ∃ hlen : out.1.length = pat.length + 1,
      FailurePrefix pat out.1 pat.length (by omega) hlen ∧
      (∀ (i : Nat) (hi : i < out.1.length), Int.toNat (out.1[i]'hi) < pat.length) ∧
      (∀ (i : Nat) (hi : i < out.1.length), -1 ≤ out.1[i]'hi) ∧
      (∀ (i : Nat) (hi : i < out.1.length), Int.toNat (out.1[i]'hi + 1) ≤ i) ∧
      0 ≤ out.2 ∧
      LongestBorder pat pat.length (Int.toNat out.2) := by
  induction fuel generalizing pos cnd table with
  | zero =>
      exfalso
      omega
  | succ fuel ih =>
      rcases hinv with ⟨hcndNonneg, hprefix, hlong⟩
      set entry := lpsStepEntry pos cnd pat table hpos hcndPat hcndTable
      set table' := table.set pos entry
      set nextCnd := lpsStepFallback pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound + 1
      have hstepRes :
          ∃ hlen : table'.length = pat.length + 1,
            FailurePrefix pat table' (pos + 1) (by omega) hlen ∧
            (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi) < pat.length) ∧
            (∀ (i : Nat) (hi : i < table'.length), -1 ≤ table'[i]'hi) ∧
            (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi + 1) ≤ i) ∧
            0 ≤ nextCnd ∧
            LongestBorder pat (pos + 1) (Int.toNat nextCnd) := by
        simpa [entry, table', nextCnd] using
          lpsStep_invariant pos cnd pat table
            hpos hcndPat hcndTable htableLen htableBound
            hcndNonneg hcndStep hprefix hlong htableLower htableStep
      rcases hstepRes with ⟨hlen, hprefix', hbound', hlower', hstep', hnextNonneg, hlong'⟩
      by_cases hnextPos : pos + 1 < pat.length
      · have hnextPat : Int.toNat nextCnd < pat.length := by
          calc
            Int.toNat nextCnd < pos + 1 := hlong'.1.1
            _ < pat.length := hnextPos
        have hnextTable : Int.toNat nextCnd < table'.length := by
          calc
            Int.toNat nextCnd < pat.length := hnextPat
            _ < pat.length + 1 := Nat.lt_succ_self _
            _ = table'.length := hlen.symm
        have hnextStep : Int.toNat (nextCnd + 1) ≤ pos + 1 := by
          rw [int_toNat_add_one_eq hnextNonneg]
          exact Nat.succ_le_of_lt hlong'.1.1
        have hinv' : LPSInvariant pat (pos + 1) nextCnd table' hnextPos hnextPat hlen :=
          ⟨hnextNonneg, hprefix', hlong'⟩
        have hrec := ih (pos + 1) nextCnd table'
          hnextPos hnextPat hnextTable hlen hbound' (by omega) hinv' hnextStep hlower' hstep'
        have heval :
            (LPSWhile (fuel + 1) pos cnd pat table
              hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost =
            (LPSWhile fuel (pos + 1) nextCnd pat table'
              hnextPos hnextPat hnextTable hlen hbound').eval Comparison.natCost := by
          by_cases hcmp : pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat
          · have hnextPat' : Int.toNat (cnd + 1) < pat.length := by
              simpa [nextCnd, lpsStepFallback, hcmp] using hnextPat
            simp [LPSWhile, Prog.eval, entry, table', nextCnd, lpsStepEntry, lpsStepFallback,
              hnextPos, hcmp, hnextPat']
          · have hnextPat' :
              Int.toNat
                ((innerLPSWhile table.length pos (table[Int.toNat cnd]'hcndTable) pat table
                  hpos (htableBound (Int.toNat cnd) hcndTable)
                  (by
                    calc
                      Int.toNat (table[Int.toNat cnd]'hcndTable) < pat.length :=
                        htableBound (Int.toNat cnd) hcndTable
                      _ < pat.length + 1 := Nat.lt_succ_self _
                      _ = table.length := htableLen.symm)
                  htableLen htableBound).eval Comparison.natCost + 1) < pat.length := by
              simpa [nextCnd, lpsStepFallback, hcmp] using hnextPat
            simp [LPSWhile, entry, table', nextCnd, lpsStepEntry, lpsStepFallback,
              hnextPos, hcmp, hnextPat']
        simpa [heval] using hrec
      · have hfinal : pos + 1 = pat.length := by omega
        have hprefixFinal : FailurePrefix pat table' pat.length (by omega) hlen := by
          simpa [hfinal] using hprefix'
        have hlongFinal : LongestBorder pat pat.length (Int.toNat nextCnd) := by
          simpa [hfinal] using hlong'
        have hres :
            ∃ hlen : table'.length = pat.length + 1,
              FailurePrefix pat table' pat.length (by omega) hlen ∧
              (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi) < pat.length) ∧
              (∀ (i : Nat) (hi : i < table'.length), -1 ≤ table'[i]'hi) ∧
              (∀ (i : Nat) (hi : i < table'.length), Int.toNat (table'[i]'hi + 1) ≤ i) ∧
              0 ≤ nextCnd ∧
              LongestBorder pat pat.length (Int.toNat nextCnd) :=
          ⟨hlen, hprefixFinal, hbound', hlower', hstep', hnextNonneg, hlongFinal⟩
        have heval :
            (LPSWhile (fuel + 1) pos cnd pat table
              hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost =
            (table', nextCnd) := by
          rcases Decidable.em (pat[pos]'hpos == pat[Int.toNat cnd]'hcndPat) with hcmp | hcmp <;>
            simp [LPSWhile, Prog.eval, entry, table', nextCnd, lpsStepEntry, lpsStepFallback,
              hnextPos, hcmp]
        simpa [heval] using hres

private lemma LPSWhile_final [BEq α] [LawfulBEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length) (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi) < pat.length)
    (hcndNonneg : 0 ≤ cnd) (hcndStep : Int.toNat (cnd + 1) ≤ pos)
    (hprefix : FailurePrefix pat table pos hpos.le htableLen)
    (hlong : LongestBorder pat pos (Int.toNat cnd))
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi + 1) ≤ i)
    (hremain : pos + fuel = pat.length) :
    let res := (LPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost
    let table' := res.1
    let cnd' := res.2
    ∃ hlen : table'.length = pat.length + 1,
      FailurePrefix pat table' pat.length (by omega) hlen ∧
      0 ≤ cnd' ∧
      LongestBorder pat pat.length (Int.toNat cnd') := by
  rcases LPSWhile_eval_invariant fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound (by omega)
      ⟨hcndNonneg, hprefix, hlong⟩ hcndStep htableLower htableStep with
    ⟨hlen, hprefix', _, _, _, hcndNonneg', hlong'⟩
  exact ⟨hlen, hprefix', hcndNonneg', hlong'⟩

private lemma failurePrefix_set_sentinel [BEq α] {pat : List α} {table : List Int}
    (htableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pat.length (by omega) htableLen)
    (entry : Int) :
    ∃ hlen : (table.set pat.length entry).length = pat.length + 1,
      FailurePrefix pat (table.set pat.length entry) pat.length (by omega) hlen := by
  refine ⟨by simpa [List.length_set] using htableLen, ?_⟩
  intro i hi
  have hNe : pat.length ≠ i := by omega
  have hj : i < (table.set pat.length entry).length := by
    simpa [List.length_set, htableLen] using (show i < pat.length + 1 by omega)
  have hget :
      (table.set pat.length entry)[i]'hj =
        table[i]'(by simpa [List.length_set, htableLen] using hj) := by
    simpa using
      List.getElem_set_of_ne (l := table) (i := pat.length) (j := i) (h := hNe) entry hj
  have hfp :
      FailureEntry pat i (by omega)
        (table[i]'(by simpa [List.length_set, htableLen] using hj)) := by
    simpa using hprefix i hi
  simpa [hget] using hfp

private lemma buildLPS_failurePrefix [BEq α] [LawfulBEq α] {pat : List α} (h1 : 1 < pat.length) :
    ∃ hlen : ((buildLPS pat).eval Comparison.natCost).length = pat.length + 1,
      FailurePrefix pat ((buildLPS pat).eval Comparison.natCost) pat.length (by omega) hlen := by
  cases pat with
  | nil =>
      simp at h1
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h1
      | cons y ys =>
          let pat' := x :: y :: ys
          let table0 : List Int := -1 :: List.replicate pat'.length 0
          have hpos : 1 < pat'.length := by simp [pat']
          have hcndPat : Int.toNat (0 : Int) < pat'.length := by simp [pat']
          have hcndTable : Int.toNat (0 : Int) < table0.length := by simp [pat', table0]
          have htableLen : table0.length = pat'.length + 1 := by simp [pat', table0]
          rcases initTable0_bound pat' (by simp [pat']) with
            ⟨htableBound, htableLower, htableStep, _⟩
          have hinit : FailurePrefix pat' table0 1 hpos.le htableLen := by
            simpa [pat', table0] using
              initial_failurePrefix (pat := pat') (by simp [pat'])
          rcases LPSWhile_final (ys.length + 1) 1 0 pat' table0
            hpos hcndPat hcndTable htableLen htableBound
            (by omega) (by simp) hinit longestBorder_one
            htableLower htableStep
            (by simp [pat', Nat.add_comm, Nat.add_left_comm])
            with ⟨hlen, hprefix, _, _⟩
          let res : List Int × Int :=
            (LPSWhile (ys.length + 1) 1 0 pat' table0
              hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost
          let table1 : List Int := res.1
          let cnd1 : Int := res.2
          have hlen1 : table1.length = pat'.length + 1 := by
            simpa [res, table1] using hlen
          have hprefix1 : FailurePrefix pat' table1 pat'.length (by omega) hlen1 := by
            simpa [res, table1, hlen1] using hprefix
          rcases failurePrefix_set_sentinel (pat := pat') (table := table1) hlen1 hprefix1 cnd1 with
            ⟨hbuildLen, hbuildPrefix⟩
          refine ⟨?_, ?_⟩
          · simpa [pat', buildLPS, table0, res, table1, cnd1] using hbuildLen
          · simpa [pat', buildLPS, table0, res, table1, cnd1] using hbuildPrefix

private lemma buildLPS_failurePrefix_all [BEq α] [LawfulBEq α] (pat : List α) :
    ∃ hlen : ((buildLPS pat).eval Comparison.natCost).length = pat.length + 1,
      FailurePrefix pat ((buildLPS pat).eval Comparison.natCost) pat.length (by omega) hlen := by
  cases pat with
  | nil =>
      refine ⟨by simp [buildLPS], ?_⟩
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
  | cons x xs =>
      cases xs with
      | nil =>
          refine ⟨by simp [buildLPS], ?_⟩
          intro i hi
          cases i with
          | zero =>
              simpa [buildLPS] using
                (failureEntry_zero (pat := ([x] : List α)) (h0 := by simp))
          | succ i =>
              simp at hi
      | cons y ys =>
          simpa using
            (buildLPS_failurePrefix (pat := x :: y :: ys) (h1 := by simp))

private lemma buildLPS_length [BEq α] [LawfulBEq α] (pat : List α) :
    ((buildLPS pat).eval Comparison.natCost).length = pat.length + 1 :=
  (buildLPS_failurePrefix_all (pat := pat)).1

private lemma buildLPS_sentinel_longest_nontrivial [BEq α] [LawfulBEq α]
    {pat : List α} (h1 : 1 < pat.length) :
    0 ≤ ((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
      have hlen := buildLPS_length (pat := pat)
      omega) ∧
    LongestBorder pat pat.length
      (Int.toNat (((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
        have hlen := buildLPS_length (pat := pat)
        omega))) := by
  cases pat with
  | nil =>
      simp at h1
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h1
      | cons y ys =>
          let pat' := x :: y :: ys
          let table0 : List Int := -1 :: List.replicate pat'.length 0
          have hpos : 1 < pat'.length := by simp [pat']
          have hcndPat : Int.toNat (0 : Int) < pat'.length := by simp [pat']
          have hcndTable : Int.toNat (0 : Int) < table0.length := by simp [pat', table0]
          have htableLen : table0.length = pat'.length + 1 := by simp [pat', table0]
          rcases initTable0_bound pat' (by simp [pat']) with
            ⟨htableBound, htableLower, htableStep, _⟩
          have hinit : FailurePrefix pat' table0 1 hpos.le htableLen := by
            simpa [pat', table0] using
              initial_failurePrefix (pat := pat') (by simp [pat'])
          rcases LPSWhile_final (ys.length + 1) 1 0 pat' table0
            hpos hcndPat hcndTable htableLen htableBound
            (by omega) (by simp) hinit longestBorder_one
            htableLower htableStep
            (by simp [pat', Nat.add_comm, Nat.add_left_comm])
            with ⟨hlen, _, hcndNonneg, hlong⟩
          let res : List Int × Int :=
            (LPSWhile (ys.length + 1) 1 0 pat' table0
              hpos hcndPat hcndTable htableLen htableBound).eval Comparison.natCost
          let table1 : List Int := res.1
          let cnd1 : Int := res.2
          have hlen1 : table1.length = pat'.length + 1 := by
            simpa [res, table1] using hlen
          have hsentinel :
              (table1.set pat'.length cnd1)[pat'.length]'(by
                simp [List.length_set, hlen1]) = cnd1 := by
            exact
              List.getElem_set_self (l := table1) (i := pat'.length) (a := cnd1)
                (by simp [List.length_set, hlen1])
          constructor
          · simpa [buildLPS, pat', table0, res, table1, cnd1, hsentinel] using hcndNonneg
          · simpa [buildLPS, pat', table0, res, table1, cnd1, hsentinel] using hlong

private lemma buildLPS_sentinel_longest_nonempty [BEq α] [LawfulBEq α]
    {pat : List α} (h0 : 0 < pat.length) :
    0 ≤ ((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
      have hlen := buildLPS_length (pat := pat)
      omega) ∧
    LongestBorder pat pat.length
      (Int.toNat (((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
        have hlen := buildLPS_length (pat := pat)
        omega))) := by
  by_cases h1 : 1 < pat.length
  · exact buildLPS_sentinel_longest_nontrivial h1
  · cases pat with
    | nil =>
        simp at h0
    | cons x xs =>
        cases xs with
        | nil =>
            constructor
            · simp [buildLPS]
            · simpa [buildLPS] using (longestBorder_one (pat := ([x] : List α)))
        | cons y ys =>
            exfalso
            exact h1 (by simp)

private lemma buildLPS_spec [BEq α] [LawfulBEq α] (pat : List α) :
    ∃ hlen : ((buildLPS pat).eval Comparison.natCost).length = pat.length + 1,
      FailurePrefix pat ((buildLPS pat).eval Comparison.natCost) pat.length (by omega) hlen ∧
      (0 < pat.length →
        let sentinel := ((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
          have _hlen := buildLPS_length (pat := pat)
          omega)
        0 ≤ sentinel ∧
        LongestBorder pat pat.length (Int.toNat sentinel) ∧
        (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
          | some suffixLen => Int.toNat suffixLen
          | none => 0) = Int.toNat sentinel ∧
        (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
          | some suffixLen => Int.toNat suffixLen
          | none => 0) < pat.length) := by
  rcases buildLPS_failurePrefix_all (pat := pat) with ⟨hlen, hprefix⟩
  refine ⟨hlen, hprefix, ?_⟩
  intro h0
  let sentinel :=
    ((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
      have _hlen := buildLPS_length (pat := pat)
      omega)
  have hsentinel :
      0 ≤ sentinel ∧ LongestBorder pat pat.length (Int.toNat sentinel) := by
    dsimp [sentinel]
    exact buildLPS_sentinel_longest_nonempty (pat := pat) h0
  have hsentinelGet? :
      ((buildLPS pat).eval Comparison.natCost)[pat.length]? = some sentinel := by
    dsimp [sentinel]
    exact
      List.getElem?_eq_getElem (l := (buildLPS pat).eval Comparison.natCost)
        (i := pat.length)
        (by
          have _hlen := buildLPS_length (pat := pat)
          omega)
  have hresetEq :
      (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
        | some suffixLen => Int.toNat suffixLen
        | none => 0) = Int.toNat sentinel := by
    simp [hsentinelGet?]
  have hresetLt :
      (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
        | some suffixLen => Int.toNat suffixLen
        | none => 0) < pat.length := by
    rw [hresetEq]
    exact hsentinel.2.1.1
  exact ⟨hsentinel.1, hsentinel.2, hresetEq, hresetLt⟩

private lemma kmpSearchPositionsAux_eval_cons [BEq α]
    (t : α) (ts : List α) (j k : Nat) (pat : List α) (table : List Int) (accRev : List Nat) :
    (kmpSearchPositionsAux (t :: ts) j k pat table accRev).eval Comparison.natCost =
      match (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
      | none =>
          (kmpSearchPositionsAux ts (j + 1) 0 pat table accRev).eval Comparison.natCost
      | some k' =>
          let nextK := k' + 1
          if nextK = pat.length then
            let start := j + 1 - pat.length
            let reset :=
              match table[pat.length]? with
              | some suffixLen => Int.toNat suffixLen
              | none => 0
            (kmpSearchPositionsAux ts (j + 1) reset pat table (start :: accRev)).eval
              Comparison.natCost
          else
            (kmpSearchPositionsAux ts (j + 1) nextK pat table accRev).eval Comparison.natCost := by
  cases hmatched : (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
  | none =>
      simp [kmpSearchPositionsAux, Prog.eval_bind, hmatched]
  | some k' =>
      rcases Decidable.em (k' + 1 = pat.length) with hnext | hnext <;>
        simp [kmpSearchPositionsAux, Prog.eval_bind, hmatched, hnext]

private lemma kmpSearchPositionsAux_eval_append_acc [BEq α]
    (txt : List α) (j k : Nat) (pat : List α) (table : List Int) (accRev : List Nat) :
    (kmpSearchPositionsAux txt j k pat table accRev).eval Comparison.natCost =
      accRev.reverse ++ (kmpSearchPositionsAux txt j k pat table []).eval Comparison.natCost := by
  induction txt generalizing j k accRev with
  | nil =>
      simp [kmpSearchPositionsAux]
  | cons t ts ih =>
      cases hmatched : (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
      | none =>
          rw [kmpSearchPositionsAux_eval_cons t ts j k pat table accRev]
          rw [kmpSearchPositionsAux_eval_cons t ts j k pat table ([] : List Nat)]
          simpa [hmatched] using ih (j := j + 1) (k := 0) (accRev := accRev)
      | some k' =>
          by_cases hnext : k' + 1 = pat.length
          · rw [kmpSearchPositionsAux_eval_cons t ts j k pat table accRev]
            rw [kmpSearchPositionsAux_eval_cons t ts j k pat table ([] : List Nat)]
            set start : Nat := j + 1 - pat.length
            set reset : Nat :=
              match table[pat.length]? with
              | some suffixLen => Int.toNat suffixLen
              | none => 0
            have hacc := ih (j := j + 1) (k := reset) (accRev := start :: accRev)
            have hone := ih (j := j + 1) (k := reset) (accRev := [start])
            rw [hacc, hone]
            simp [hmatched, hnext, List.reverse_cons, List.append_assoc]
          · rw [kmpSearchPositionsAux_eval_cons t ts j k pat table accRev]
            rw [kmpSearchPositionsAux_eval_cons t ts j k pat table ([] : List Nat)]
            simpa [hmatched, hnext] using ih (j := j + 1) (k := k' + 1) (accRev := accRev)

private def FallbackCandidate (pat : List α) (k l : Nat) : Prop :=
  l = k ∨ Border pat k l

private lemma failurePrefix_entry_at [BEq α]
    {pat : List α} {table : List Int}
    (hTableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
    {k : Nat} (hk : k < pat.length) :
    FailureEntry pat k hk (table[k]'(by omega)) :=
  hprefix k hk

private lemma getElem_eq_of_getElem?_eq_some
    {xs : List α} {i : Nat} (hi : i < xs.length) {x : α}
    (h : xs[i]? = some x) :
    xs[i]'hi = x :=
  Option.some.inj (by rw [← List.getElem?_eq_getElem hi, h])

private lemma failureEntry_of_table_get? [BEq α]
    {pat : List α} {table : List Int}
    (hTableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
    {k : Nat} (hk : k < pat.length) {nextK : Int}
    (hnext : table[k]? = some nextK) :
    FailureEntry pat k hk nextK := by
  have hkTable : k < table.length := by omega
  have hEntry0 : FailureEntry pat k hk (table[k]'hkTable) :=
    failurePrefix_entry_at hTableLen hprefix hk
  have hvalEq : table[k]'hkTable = nextK :=
    getElem_eq_of_getElem?_eq_some (xs := table) hkTable hnext
  simpa [hvalEq] using hEntry0

private lemma beq_false_of_same_getElem? [BEq α] [LawfulBEq α]
    {xs : List α} {i : Nat} (hi : i < xs.length)
    {a b : α} (hneq : ¬ a == b)
    (ha : xs[i]? = some a) (hb : xs[i]? = some b) : False := by
  have ha' : xs[i]'hi = a := getElem_eq_of_getElem?_eq_some hi ha
  have hb' : xs[i]'hi = b := getElem_eq_of_getElem?_eq_some hi hb
  have hab : a = b := ha'.symm.trans hb'
  exact hneq (by simp [hab])

private lemma kmpSearchFallback_eval_full_spec [BEq α] [LawfulBEq α]
  {pat : List α} {table : List Int}
  (hTableLen : table.length = pat.length + 1)
  (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
  (t : α) {k : Nat} (hk : k < pat.length) :
  match (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
  | none =>
    ∀ l, FallbackCandidate pat k l → pat[l]? ≠ some t
  | some k' =>
    FallbackCandidate pat k k' ∧
      pat[k']? = some t ∧
      ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
  have hsomeCandidate :
      ∀ (fuel : Nat) (k : Nat), (hk : k < pat.length) →
        ∀ {k' : Nat},
          (kmpSearchFallback fuel t k pat table).eval Comparison.natCost = some k' →
            FallbackCandidate pat k k' ∧
              pat[k']? = some t ∧
              ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
    intro fuel k hk k' hres
    induction fuel generalizing k hk with
    | zero =>
        simp [kmpSearchFallback] at hres
    | succ fuel ih =>
        cases hpk : pat[k]? with
        | none =>
            simp [kmpSearchFallback, hpk] at hres
        | some pk =>
            by_cases hcmp : pk == t
            · have hsome : some k = some k' := by
                simpa [kmpSearchFallback, hpk, hcmp] using hres
              rcases Option.some.inj hsome with rfl
              refine ⟨Or.inl rfl, ?_, ?_⟩
              · have hkGet : pat[k]'hk = pk := getElem_eq_of_getElem?_eq_some (xs := pat) hk hpk
                have hEq : pat[k]'hk = t := hkGet.trans (eq_of_beq hcmp)
                simpa [hEq] using (List.getElem?_eq_getElem hk)
              · intro l hCandL _
                rcases hCandL with hEqL | hBorderL
                · cases hEqL
                  exact le_rfl
                · exact Nat.le_of_lt hBorderL.1
            · cases hnext : table[k]? with
              | none =>
                  simp [kmpSearchFallback, hpk, hcmp, hnext] at hres
              | some nextK =>
                  by_cases hneg : nextK < 0
                  · have hnone : none = some k' := by
                      simp [kmpSearchFallback, hpk, hcmp, hnext, hneg] at hres
                    cases hnone
                  · have hrec :
                        (kmpSearchFallback fuel t (Int.toNat nextK) pat table).eval
                          Comparison.natCost = some k' := by
                      simpa [kmpSearchFallback, hpk, hcmp, hnext, hneg] using hres
                    have hnonneg : 0 ≤ nextK := by omega
                    have hEntry : FailureEntry pat k hk nextK :=
                      failureEntry_of_table_get? hTableLen hprefix hk hnext
                    have hkNextLtK : Int.toNat nextK < k := failureEntry_target_lt hEntry hnonneg
                    have hkNext : Int.toNat nextK < pat.length := lt_trans hkNextLtK hk
                    rcases ih (k := Int.toNat nextK) (hk := hkNext) hrec with
                      ⟨hCandRec, hCharRec, hMaxRec⟩
                    have hneg' : ¬ nextK < 0 := by omega
                    have hEntryPos :
                        ∃ hn : Border pat k (Int.toNat nextK),
                          pat[k]'hk ≠ pat[Int.toNat nextK]'(lt_trans hn.1 hk) ∧
                          ∀ l, (hl : Border pat k l) →
                            pat[k]'hk ≠ pat[l]'(lt_trans hl.1 hk) → l ≤ Int.toNat nextK := by
                      simpa [FailureEntry, hneg'] using hEntry
                    rcases hEntryPos with ⟨hnBorder, _, hEntryMax⟩
                    have hCand : FallbackCandidate pat k k' := by
                      rcases hCandRec with hEqRec | hBorderRec
                      · right
                        simpa [hEqRec] using hnBorder
                      · right
                        exact border_trans hnBorder hBorderRec
                    have hMax :
                        ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
                      intro l hCandL hCharL
                      rcases hCandL with hEqL | hBorderL
                      · exfalso
                        cases hEqL
                        exact False.elim
                          (beq_false_of_same_getElem? (xs := pat) hk hcmp hpk hCharL)
                      · have hl : l < pat.length := (List.getElem?_eq_some_iff.mp hCharL).1
                        have hEqL : pat[l]'(lt_trans hBorderL.1 hk) = t :=
                          getElem_eq_of_getElem?_eq_some
                            (xs := pat) (lt_trans hBorderL.1 hk) hCharL
                        have hkGet : pat[k]'hk = pk :=
                          getElem_eq_of_getElem?_eq_some (xs := pat) hk hpk
                        have hneKL : pat[k]'hk ≠ pat[l]'(lt_trans hBorderL.1 hk) := by
                          intro hEq
                          have hpkEq : pk = t := hkGet.symm.trans (hEq.trans hEqL)
                          exact hcmp (by simp [hpkEq])
                        have hleN : l ≤ Int.toNat nextK := hEntryMax l hBorderL hneKL
                        have hCandN : FallbackCandidate pat (Int.toNat nextK) l := by
                          by_cases hEqN : l = Int.toNat nextK
                          · exact Or.inl hEqN
                          · have hltN : l < Int.toNat nextK := by omega
                            exact Or.inr (border_of_longest_prefix hnBorder hBorderL hltN)
                        exact hMaxRec l hCandN hCharL
                    exact ⟨hCand, hCharRec, hMax⟩
  have hsomeOfCandidate :
      ∀ {k : Nat}, (hk : k < pat.length) →
        (∃ l, FallbackCandidate pat k l ∧ pat[l]? = some t) →
        ∀ fuel, k + 1 ≤ fuel →
          ∃ k', (kmpSearchFallback fuel t k pat table).eval Comparison.natCost = some k' := by
    intro k
    refine Nat.strong_induction_on k ?_
    intro k ih hk hCand fuel hFuel
    cases fuel with
    | zero =>
        omega
    | succ fuel =>
        cases hpk : pat[k]? with
        | none =>
            exfalso
            have hpkSome : pat[k]? = some (pat[k]'hk) := by
              rw [List.getElem?_eq_getElem hk]
            simp [hpk] at hpkSome
        | some pk =>
            by_cases hcmp : pk == t
            · refine ⟨k, ?_⟩
              simp [kmpSearchFallback, hpk, hcmp]
            · rcases hCand with ⟨l, hCandL, hCharL⟩
              rcases hCandL with hEqL | hBorderL
              · exfalso
                cases hEqL
                exact False.elim
                  (beq_false_of_same_getElem? (xs := pat) hk hcmp hpk hCharL)
              · cases hnext : table[k]? with
                | none =>
                    exfalso
                    have hkTable : k < table.length := by omega
                    have hnextSome : table[k]? = some (table[k]'hkTable) := by
                      rw [List.getElem?_eq_getElem hkTable]
                    simp [hnext] at hnextSome
                | some nextK =>
                    by_cases hneg : nextK < 0
                    · exfalso
                      have hEntry : FailureEntry pat k hk nextK :=
                        failureEntry_of_table_get? hTableLen hprefix hk hnext
                      have hAllEq :
                          ∀ l, (hl : Border pat k l) →
                            pat[k]'hk = pat[l]'(lt_trans hl.1 hk) := by
                        simpa [FailureEntry, hneg] using hEntry
                      have hEqL : pat[l]'(lt_trans hBorderL.1 hk) = t :=
                        getElem_eq_of_getElem?_eq_some
                          (xs := pat) (lt_trans hBorderL.1 hk) hCharL
                      have hkGet : pat[k]'hk = pk :=
                        getElem_eq_of_getElem?_eq_some (xs := pat) hk hpk
                      have hEqKL : pat[k]'hk = pat[l]'(lt_trans hBorderL.1 hk) := hAllEq l hBorderL
                      have hpkEq : pk = t := hkGet.symm.trans (hEqKL.trans hEqL)
                      exact hcmp (by simp [hpkEq])
                    · have hnonneg : 0 ≤ nextK := by omega
                      have hEntry : FailureEntry pat k hk nextK :=
                        failureEntry_of_table_get? hTableLen hprefix hk hnext
                      have hkNextLtK : Int.toNat nextK < k := failureEntry_target_lt hEntry hnonneg
                      have hkNext : Int.toNat nextK < pat.length := lt_trans hkNextLtK hk
                      have hneg' : ¬ nextK < 0 := by omega
                      have hEntryPos :
                          ∃ hn : Border pat k (Int.toNat nextK),
                            pat[k]'hk ≠ pat[Int.toNat nextK]'(lt_trans hn.1 hk) ∧
                            ∀ l0, (hl0 : Border pat k l0) →
                              pat[k]'hk ≠ pat[l0]'(lt_trans hl0.1 hk) → l0 ≤ Int.toNat nextK := by
                        simpa [FailureEntry, hneg'] using hEntry
                      rcases hEntryPos with ⟨hnBorder, _, hEntryMax⟩
                      have hEqL : pat[l]'(lt_trans hBorderL.1 hk) = t :=
                        getElem_eq_of_getElem?_eq_some
                          (xs := pat) (lt_trans hBorderL.1 hk) hCharL
                      have hkGet : pat[k]'hk = pk :=
                        getElem_eq_of_getElem?_eq_some (xs := pat) hk hpk
                      have hneKL : pat[k]'hk ≠ pat[l]'(lt_trans hBorderL.1 hk) := by
                        intro hEq
                        have hpkEq : pk = t := hkGet.symm.trans (hEq.trans hEqL)
                        exact hcmp (by simp [hpkEq])
                      have hleN : l ≤ Int.toNat nextK := hEntryMax l hBorderL hneKL
                      have hCandN :
                          ∃ l0, FallbackCandidate pat (Int.toNat nextK) l0 ∧ pat[l0]? = some t := by
                        refine ⟨l, ?_, hCharL⟩
                        by_cases hEqN : l = Int.toNat nextK
                        · exact Or.inl hEqN
                        · have hltN : l < Int.toNat nextK := by omega
                          exact Or.inr (border_of_longest_prefix hnBorder hBorderL hltN)
                      have hkLeFuel : k ≤ fuel := by omega
                      have hFuelNext : Int.toNat nextK + 1 ≤ fuel := by omega
                      rcases ih (Int.toNat nextK) hkNextLtK hkNext hCandN fuel hFuelNext with
                        ⟨k'', hk''⟩
                      refine ⟨k'', ?_⟩
                      simp [kmpSearchFallback, hpk, hcmp, hnext, hneg, hk'']
  have hfallbackTools :
      (∀ (fuel : Nat) (k : Nat), (hk : k < pat.length) →
        ∀ {k' : Nat},
          (kmpSearchFallback fuel t k pat table).eval Comparison.natCost = some k' →
            FallbackCandidate pat k k' ∧
              pat[k']? = some t ∧
              ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k') ∧
      (∀ {k : Nat}, (hk : k < pat.length) →
        (∃ l, FallbackCandidate pat k l ∧ pat[l]? = some t) →
        ∀ fuel, k + 1 ≤ fuel →
          ∃ k', (kmpSearchFallback fuel t k pat table).eval Comparison.natCost = some k') :=
    ⟨hsomeCandidate, hsomeOfCandidate⟩
  cases hres : (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
  | none =>
    intro l hCand hChar
    have hFuel : k + 1 ≤ table.length := by omega
    have hExists : ∃ l0, FallbackCandidate pat k l0 ∧ pat[l0]? = some t :=
      ⟨l, hCand, hChar⟩
    rcases hfallbackTools.2 hk hExists table.length hFuel with
      ⟨k', hSome⟩
    rw [hres] at hSome
    cases hSome
  | some k' =>
    exact hfallbackTools.1 table.length k hk hres

private def FrontierState (pat pref : List α) (k : Nat) : Prop :=
  k ≤ pref.length ∧
    pat.take k = pref.drop (pref.length - k) ∧
    ∀ l, l < pat.length →
      l ≤ pref.length →
      pat.take l = pref.drop (pref.length - l) → l ≤ k

private lemma fallbackCandidate_le {pat : List α} {k l : Nat}
    (hCand : FallbackCandidate pat k l) :
    l ≤ k := by
  rcases hCand with rfl | hBorder
  · exact le_refl _
  · exact Nat.le_of_lt hBorder.1

private lemma suffix_succ_iff {pat pref : List α} {l : Nat} {t : α}
    (hl : l < pat.length) (hlPref : l ≤ pref.length) :
    pat.take (l + 1) = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) ↔
      pat.take l = pref.drop (pref.length - l) ∧ pat[l]? = some t := by
  constructor
  · intro hsuf
    have hsuf' : pat.take l ++ [pat[l]'hl] = pref.drop (pref.length - l) ++ [t] := by
      calc
        pat.take l ++ [pat[l]'hl] = pat.take (l + 1) := by
          -- simpa using (List.take_concat_get' pat l hl)
          simp [List.take_concat_get' pat l hl]
        _ = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) := hsuf
        _ = pref.drop (pref.length - l) ++ [t] := by
          simp [List.drop_append]
    have hlenPat : (pat.take l).length = l := by
      simp [Nat.min_eq_left (Nat.le_of_lt hl)]
    have hlenPref : (pref.drop (pref.length - l)).length = l := by
      rw [List.length_drop]
      omega
    have hlen : (pat.take l).length = (pref.drop (pref.length - l)).length := by
      omega
    have hpair := List.append_inj hsuf' hlen
    refine ⟨hpair.1, ?_⟩
    rw [List.getElem?_eq_getElem hl]
    simpa using hpair.2
  · intro h
    rcases h with ⟨hsuf, hchar⟩
    have hEq : pat[l]'hl = t := by
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem hl, hchar]
    calc
      pat.take (l + 1) = pat.take l ++ [pat[l]'hl] := by
        simp [List.take_concat_get' pat l hl]
      _ = pref.drop (pref.length - l) ++ [t] := by simp [hsuf, hEq]
      _ = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) := by
        have hidx : (pref ++ [t]).length - (l + 1) = pref.length - l := by
          simp
        have hdrop :
            (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) =
              pref.drop (pref.length - l) ++ [t] := by
          simp [List.drop_append]
        simpa [hdrop] using hdrop.symm

private lemma frontier_extend_of_candidate {pat pref : List α} {k l : Nat} {t : α}
    (hstate : FrontierState pat pref k)
    (hCand : FallbackCandidate pat k l)
    (hlPat : l < pat.length)
    (hChar : pat[l]? = some t) :
    pat.take (l + 1) = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) := by
  have hEqL : pat.take l = pref.drop (pref.length - l) := by
    rcases hstate with ⟨_, hEqK, _⟩
    rcases hCand with rfl | hBorder
    · exact hEqK
    · rcases hBorder with ⟨hlk, hBorderEq⟩
      calc
        pat.take l = (pat.take k).drop (k - l) := hBorderEq
        _ = (pref.drop (pref.length - k)).drop (k - l) := by simp [hEqK]
        _ = pref.drop ((pref.length - k) + (k - l)) := by rw [List.drop_drop]
        _ = pref.drop (pref.length - l) := by
          have hlk' : l ≤ k := Nat.le_of_lt hlk
          have hcalc : (pref.length - k) + (k - l) = pref.length - l := by omega
          simp [hcalc]
  have hleK : l ≤ k := fallbackCandidate_le hCand
  rcases hstate with ⟨hkPref, _, _⟩
  have hlPref : l ≤ pref.length := le_trans hleK hkPref
  exact (suffix_succ_iff hlPat hlPref).2 ⟨hEqL, hChar⟩

private lemma frontier_candidate_of_suffix_succ {pat pref : List α} {k l : Nat} {t : α}
    (hstate : FrontierState pat pref k)
    (hlPat : l < pat.length)
    (hlPref : l ≤ pref.length)
    (hsucc : pat.take (l + 1) = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1))) :
    FallbackCandidate pat k l ∧ pat[l]? = some t := by
  rcases (suffix_succ_iff (pat := pat) (pref := pref) (l := l) (t := t) hlPat hlPref).1 hsucc with
    ⟨hEqL, hChar⟩
  have hle : l ≤ k := by
    rcases hstate with ⟨_, _, hMax⟩
    exact hMax l hlPat hlPref hEqL
  have hCand : FallbackCandidate pat k l := by
    by_cases hEq : l = k
    · exact Or.inl hEq
    · have hlt : l < k := by omega
      refine Or.inr ⟨hlt, ?_⟩
      rcases hstate with ⟨_, hEqK, _⟩
      calc
        pat.take l = pref.drop (pref.length - l) := hEqL
        _ = pref.drop ((pref.length - k) + (k - l)) := by
          have hcalc : (pref.length - k) + (k - l) = pref.length - l := by omega
          simp [hcalc]
        _ = (pref.drop (pref.length - k)).drop (k - l) := by
          rw [List.drop_drop]
        _ = (pat.take k).drop (k - l) := by simp [hEqK]
  exact ⟨hCand, hChar⟩

private lemma frontierState_step_kmpSearchFallback_eval [BEq α] [LawfulBEq α]
    {pat pref : List α} {table : List Int} {k : Nat} {t : α}
    (hTableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
    (hstate : FrontierState pat pref k)
    (hkPat : k < pat.length) :
    FrontierState pat (pref ++ [t])
      (match (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
      | none => 0
      | some k' => k' + 1) := by
  cases hres : (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
  | none =>
      have hnone :
          ∀ l, FallbackCandidate pat k l → pat[l]? ≠ some t := by
        simpa [hres] using
          (kmpSearchFallback_eval_full_spec (pat := pat) (table := table)
            hTableLen hprefix t hkPat)
      have hnoneStep : FrontierState pat (pref ++ [t]) 0 := by
        refine ⟨by simp, by simp, ?_⟩
        intro l hlPat hlPref hsuf
        cases l with
        | zero =>
            omega
        | succ l' =>
            have hl'Pat : l' < pat.length := by omega
            have hlPref' : l' + 1 ≤ pref.length + 1 := by simpa using hlPref
            have hl'Pref : l' ≤ pref.length := by omega
            rcases frontier_candidate_of_suffix_succ (hstate := hstate) (l := l') (t := t)
                hl'Pat hl'Pref (by simpa using hsuf) with ⟨hCand, hChar⟩
            exact False.elim ((hnone l' hCand) hChar)
      simpa [hres] using hnoneStep
  | some k' =>
      have hsome :
          FallbackCandidate pat k k' ∧
            pat[k']? = some t ∧
            ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
        simpa [hres] using
          (kmpSearchFallback_eval_full_spec (pat := pat) (table := table)
            hTableLen hprefix t hkPat)
      rcases hsome with ⟨hCand, hChar, hMaxCand⟩
      have hk'Pat : k' < pat.length := lt_of_le_of_lt (fallbackCandidate_le hCand) hkPat
      have hsomeStep : FrontierState pat (pref ++ [t]) (k' + 1) := by
        refine ⟨?_, ?_, ?_⟩
        · have hk'Pref : k' ≤ pref.length := le_trans (fallbackCandidate_le hCand) hstate.1
          simpa using Nat.succ_le_succ hk'Pref
        · exact frontier_extend_of_candidate (hstate := hstate) hCand hk'Pat hChar
        · intro l hlPat hlPref hsuf
          cases l with
          | zero =>
              omega
          | succ l' =>
              have hl'Pat : l' < pat.length := by omega
              have hlPref' : l' + 1 ≤ pref.length + 1 := by simpa using hlPref
              have hl'Pref : l' ≤ pref.length := by omega
              rcases frontier_candidate_of_suffix_succ (hstate := hstate) (l := l') (t := t)
                  hl'Pat hl'Pref (by simpa using hsuf) with ⟨hCandL, hCharL⟩
              have hle : l' ≤ k' := hMaxCand l' hCandL hCharL
              omega
      simpa [hres] using hsomeStep

private lemma frontierState_reset_buildLPS_nonempty [BEq α] [LawfulBEq α]
    {pat pref : List α}
    (h0 : 0 < pat.length)
    (hstateFull : FrontierState pat pref pat.length) :
    FrontierState pat pref
      (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
      | some suffixLen => Int.toNat suffixLen
      | none => 0) := by
  rcases buildLPS_spec (pat := pat) with ⟨_, _, hspec⟩
  let r : Nat :=
    Int.toNat (((buildLPS pat).eval Comparison.natCost)[pat.length]'(by
      have hlen := buildLPS_length (pat := pat)
      omega))
  have hs := hspec h0
  have hrEq :
      (match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
      | some suffixLen => Int.toNat suffixLen
      | none => 0) = r := by
    simpa [r] using hs.2.2.1
  have hlong : LongestBorder pat pat.length r := by
    simpa [r] using hs.2.1
  have hstateR : FrontierState pat pref r := by
    rcases hstateFull with ⟨hpatPref, hEqFull, hmaxFull⟩
    rcases hlong with ⟨hborderR, hmaxR⟩
    have hrle : r ≤ pat.length := Nat.le_of_lt hborderR.1
    refine ⟨?_, ?_, ?_⟩
    · exact le_trans (Nat.le_of_lt hborderR.1) hpatPref
    · calc
        pat.take r = (pat.take pat.length).drop (pat.length - r) := hborderR.2
        _ = (pref.drop (pref.length - pat.length)).drop (pat.length - r) := by
              simp [hEqFull]
        _ = pref.drop ((pref.length - pat.length) + (pat.length - r)) := by
              rw [List.drop_drop]
        _ = pref.drop (pref.length - r) := by
              have hcalc : (pref.length - pat.length) + (pat.length - r) = pref.length - r := by
                have hpatPref' : pat.length ≤ pref.length := hpatPref
                have hrle' : r ≤ pat.length := hrle
                omega
              simp [hcalc]
    · intro l hlPat hlPref hsuf
      have hlle : l ≤ pat.length := Nat.le_of_lt hlPat
      have hborderL : Border pat pat.length l := by
        constructor
        · exact hlPat
        · calc
            pat.take l = pref.drop (pref.length - l) := hsuf
            _ = pref.drop ((pref.length - pat.length) + (pat.length - l)) := by
                  have hcalc : (pref.length - pat.length) + (pat.length - l) = pref.length - l := by
                    have hpatPref' : pat.length ≤ pref.length := hpatPref
                    have hlle' : l ≤ pat.length := hlle
                    omega
                  simp [hcalc]
            _ = (pref.drop (pref.length - pat.length)).drop (pat.length - l) := by
                  rw [List.drop_drop]
            _ = (pat.take pat.length).drop (pat.length - l) := by simp [hEqFull]
      exact hmaxR l hborderL
  simpa [hrEq] using hstateR

private lemma kmpSearchFallback_eval_some_full_iff_match_start [BEq α] [LawfulBEq α]
      {pat pref ts : List α} {table : List Int} {k : Nat} {t : α}
      (hTableLen : table.length = pat.length + 1)
      (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
      (hstate : FrontierState pat pref k)
      (hkPat : k < pat.length) :
      (∃ k',
        (kmpSearchFallback table.length t k pat table).eval Comparison.natCost = some k' ∧
          k' + 1 = pat.length) ↔
        pat.length ≤ (pref ++ [t]).length ∧
          pat.isPrefixOf
            ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true := by
    constructor
    · intro h
      rcases h with ⟨k', hres, hkfull⟩
      have hspec :
          FallbackCandidate pat k k' ∧
            pat[k']? = some t ∧
            ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
        simpa [hres] using
          (kmpSearchFallback_eval_full_spec (pat := pat) (table := table)
            hTableLen hprefix t hkPat)
      rcases hspec with ⟨hCand, hChar, _⟩
      have hk'Pat : k' < pat.length := lt_of_le_of_lt (fallbackCandidate_le hCand) hkPat
      have hlePref : k' + 1 ≤ (pref ++ [t]).length := by
        have hkPref : k ≤ pref.length := hstate.1
        have hk'LeK : k' ≤ k := fallbackCandidate_le hCand
        have hk'Pref : k' ≤ pref.length := le_trans hk'LeK hkPref
        simpa using Nat.succ_le_succ hk'Pref
      have hlen : pat.length ≤ (pref ++ [t]).length := by
        simpa [hkfull] using hlePref
      have hsucc :
          pat.take (k' + 1) =
            (pref ++ [t]).drop ((pref ++ [t]).length - (k' + 1)) :=
        frontier_extend_of_candidate (hstate := hstate) hCand hk'Pat hChar
      have hpatEq :
          pat = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := by
        calc
          pat = pat.take (k' + 1) := by simp [hkfull]
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - (k' + 1)) := hsucc
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := by
                simp [hkfull]
      have hdrop :
          ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) =
            (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) ++ ts := by
        have hle : (pref ++ [t]).length - pat.length ≤ (pref ++ [t]).length := by
          omega
        simpa [List.append_assoc] using
          (List.drop_append_of_le_length
            (l₁ := (pref ++ [t])) (l₂ := ts) (i := (pref ++ [t]).length - pat.length) hle)
      refine ⟨hlen, ?_⟩
      have hpref : pat <+: ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) := by
        refine ⟨ts, ?_⟩
        calc
          pat ++ ts = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) ++ ts := by
            simpa using congrArg (fun u => u ++ ts) hpatEq
          _ = ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) := hdrop.symm
      exact (List.isPrefixOf_iff_prefix).2 hpref
    · intro h
      rcases h with ⟨hlen, hmatch⟩
      have h0 : 0 < pat.length := Nat.zero_lt_of_lt hkPat
      let l : Nat := pat.length - 1
      have hlPat : l < pat.length := by
        dsimp [l]
        omega
      have hlPref : l ≤ pref.length := by
        dsimp [l]
        have hlen' : pat.length ≤ pref.length + 1 := by
          simpa using hlen
        omega
      have htake :
          pat.take pat.length =
            ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)).take pat.length := by
        have hpre' :
            pat <+: ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) :=
          (List.isPrefixOf_iff_prefix).1 (by simpa using hmatch)
        have htakeEq :
            pat =
              ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)).take pat.length :=
          (List.prefix_iff_eq_take).1 hpre'
        simpa [List.take_take] using congrArg (fun l => l.take pat.length) htakeEq
      have hdrop :
          ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)).take pat.length =
            (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := by
        have hdropFull :
            ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) =
              (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) ++ ts := by
          have hle : (pref ++ [t]).length - pat.length ≤ (pref ++ [t]).length := by
            omega
          simpa [List.append_assoc] using
            (List.drop_append_of_le_length
              (l₁ := (pref ++ [t])) (l₂ := ts) (i := (pref ++ [t]).length - pat.length) hle)
        have hlenDrop :
            ((pref ++ [t]).drop ((pref ++ [t]).length - pat.length)).length = pat.length := by
          rw [List.length_drop]
          omega
        have htakeAppend :
            (((pref ++ [t]).drop ((pref ++ [t]).length - pat.length) ++ ts).take pat.length) =
              ((pref ++ [t]).drop ((pref ++ [t]).length - pat.length)).take pat.length := by
          simpa using
            (List.take_append_of_le_length
              (l₁ := (pref ++ [t]).drop ((pref ++ [t]).length - pat.length))
              (l₂ := ts) (i := pat.length) (Nat.le_of_eq hlenDrop.symm))
        have htakeAll :
            ((pref ++ [t]).drop ((pref ++ [t]).length - pat.length)).take pat.length =
              (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) :=
          List.take_of_length_le (Nat.le_of_eq hlenDrop)
        calc
          ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)).take pat.length
              = (((pref ++ [t]).drop ((pref ++ [t]).length - pat.length) ++ ts)).take
                  pat.length := by
                    rw [hdropFull]
          _ = ((pref ++ [t]).drop ((pref ++ [t]).length - pat.length)).take pat.length := by
                simpa using htakeAppend
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := htakeAll
      have hpatEq :
          pat = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := by
        calc
          pat = pat.take pat.length := by simp
          _ = ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)).take pat.length := htake
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := hdrop
      have hlSucc : l + 1 = pat.length := by
        dsimp [l]
        omega
      have hsucc :
          pat.take (l + 1) = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) := by
        calc
          pat.take (l + 1) = pat := by simp [hlSucc]
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - pat.length) := hpatEq
          _ = (pref ++ [t]).drop ((pref ++ [t]).length - (l + 1)) := by
                simp [hlSucc]
      rcases frontier_candidate_of_suffix_succ (hstate := hstate) (l := l) (t := t)
          hlPat hlPref hsucc with ⟨hCandL, hCharL⟩
      cases hres : (kmpSearchFallback table.length t k pat table).eval Comparison.natCost with
      | none =>
          have hnone :
              ∀ l0, FallbackCandidate pat k l0 → pat[l0]? ≠ some t := by
            simpa [hres] using
              (kmpSearchFallback_eval_full_spec (pat := pat) (table := table)
                hTableLen hprefix t hkPat)
          exact False.elim ((hnone l hCandL) hCharL)
      | some k' =>
          have hspec :
              FallbackCandidate pat k k' ∧
                pat[k']? = some t ∧
                ∀ l0, FallbackCandidate pat k l0 → pat[l0]? = some t → l0 ≤ k' := by
            simpa [hres] using
              (kmpSearchFallback_eval_full_spec (pat := pat) (table := table)
                hTableLen hprefix t hkPat)
          rcases hspec with ⟨hCand, hChar, hMax⟩
          have hle : l ≤ k' := hMax l hCandL hCharL
          have hk'Pat : k' < pat.length := lt_of_le_of_lt (fallbackCandidate_le hCand) hkPat
          have hge : k' ≤ l := by
            dsimp [l]
            omega
          refine ⟨k', rfl, ?_⟩
          calc
            k' + 1 = l + 1 := by omega
            _ = pat.length := by simp [hlSucc]

private def PendingMatches [BEq α] (pat pref txt : List α) : List Nat :=
  (PatternSearchAll pat (pref ++ txt)).filter (fun i => pref.length < i + pat.length)

private lemma pendingMatches_eq_Ico_filter [BEq α] [LawfulBEq α]
    (pat pref txt : List α) :
    PendingMatches pat pref txt =
      ((List.Ico (pref.length + 1 - pat.length) (pref ++ txt).length).filter
        fun i => pat.isPrefixOf ((pref ++ txt).drop i)) := by
    unfold PendingMatches PatternSearchAll
    set w : List α := pref ++ txt
    have hpred :
        ∀ i, pref.length < i + pat.length ↔ pref.length + 1 - pat.length ≤ i := by
      intro i
      omega
    calc
      ((List.range w.length).filter fun i => pat.isPrefixOf (w.drop i)).filter
          (fun i => pref.length < i + pat.length)
          =
        ((List.Ico 0 w.length).filter fun i => pat.isPrefixOf (w.drop i)).filter
          (fun i => pref.length + 1 - pat.length ≤ i) := by
              simp [List.Ico.zero_bot, hpred]
      _ =
        (((List.Ico 0 w.length).filter
            (fun i => pref.length + 1 - pat.length ≤ i)).filter
          fun i => pat.isPrefixOf (w.drop i)) := by
              simp [List.filter_filter, Bool.and_comm]
      _ =
        ((List.Ico (pref.length + 1 - pat.length) w.length).filter
          fun i => pat.isPrefixOf (w.drop i)) := by
            simpa using
              (congrArg (fun l => l.filter (fun i => pat.isPrefixOf (w.drop i)))
                (List.Ico.filter_le 0 w.length (pref.length + 1 - pat.length)))

private lemma pendingMatches_cons [BEq α] [LawfulBEq α]
    {pat pref ts : List α} {t : α} (hpat : 0 < pat.length) :
    PendingMatches pat pref (t :: ts) =
      let hit := pat.length ≤ (pref ++ [t]).length ∧
        pat.isPrefixOf ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true
      if hit then
        (pref.length + 1 - pat.length) :: PendingMatches pat (pref ++ [t]) ts
      else
        PendingMatches pat (pref ++ [t]) ts := by
  set hit : Prop := pat.length ≤ (pref ++ [t]).length ∧
    pat.isPrefixOf ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true
  set start : Nat := pref.length + 1 - pat.length
  have hstartEq : (pref ++ [t]).length - pat.length = start := by
    simp [start]
  have hstartLt : start < (pref ++ t :: ts).length := by
    have hstartLe : start ≤ pref.length := by
      have hpat1 : 1 ≤ pat.length := Nat.succ_le_of_lt hpat
      calc
        start = pref.length + 1 - pat.length := by simp [start]
        _ ≤ pref.length + 1 - 1 := Nat.sub_le_sub_left hpat1 (pref.length + 1)
        _ = pref.length := by simp
    exact lt_of_le_of_lt hstartLe (by simp)
  by_cases hhit : hit
  · rcases hhit with ⟨hlen, hmatch⟩
    dsimp [hit]
    have hmatch' : pat.isPrefixOf ((pref ++ t :: ts).drop start) = true := by
      simpa [hstartEq] using hmatch
    have hnext : (pref ++ [t]).length + 1 - pat.length = start + 1 := by
      dsimp [start]
      omega
    have hnext' : start + 1 = pref.length + 1 + 1 - pat.length := by
      simpa using hnext.symm
    rw [pendingMatches_eq_Ico_filter, pendingMatches_eq_Ico_filter]
    rw [if_pos (by exact ⟨hlen, hmatch⟩), List.Ico.eq_cons hstartLt]
    simp [List.filter, hmatch', hnext']
  · have hcase := hhit
    dsimp [hit]
    by_cases hlen : pat.length ≤ (pref ++ [t]).length
    · have hmatch : pat.isPrefixOf ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) ≠
          true := by
        intro hm
        exact hcase ⟨hlen, hm⟩
      have hmatch' : pat.isPrefixOf ((pref ++ t :: ts).drop start) ≠ true := by
        simpa [hstartEq] using hmatch
      have hnext : (pref ++ [t]).length + 1 - pat.length = start + 1 := by
        dsimp [start]
        omega
      have hnext' : start + 1 = pref.length + 1 + 1 - pat.length := by
        simpa using hnext.symm
      rw [pendingMatches_eq_Ico_filter, pendingMatches_eq_Ico_filter]
      rw [if_neg hcase, List.Ico.eq_cons hstartLt]
      simp [List.filter, hmatch', hnext']
    · have hlt : (pref ++ [t]).length < pat.length := Nat.lt_of_not_ge hlen
      have hstart0 : start = 0 := by
        apply Nat.sub_eq_zero_of_le
        dsimp [start]
        simpa using Nat.le_of_lt hlt
      have hnext0 : (pref ++ [t]).length + 1 - pat.length = 0 :=
        Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt hlt)
      have hnext0' : pref.length + 1 + 1 - pat.length = 0 := by
        simpa using hnext0
      have hstart0' : pref.length + 1 - pat.length = 0 := by
        simpa [start] using hstart0
      rw [pendingMatches_eq_Ico_filter, pendingMatches_eq_Ico_filter]
      rw [if_neg hcase]
      simp [hstart0', hnext0']

private lemma kmpSearchPositionsAux_eval_pendingMatches [BEq α] [LawfulBEq α]
    {pat pref txt : List α} {k : Nat}
    (h0 : 0 < pat.length)
    (hkPat : k < pat.length)
    (hstate : FrontierState pat pref k) :
    (kmpSearchPositionsAux txt pref.length k pat
      ((buildLPS pat).eval Comparison.natCost) []).eval Comparison.natCost =
      PendingMatches pat pref txt := by
  rcases buildLPS_spec (pat := pat) with ⟨hTableLen, hprefix, hbuildSpec⟩
  induction txt generalizing pref k with
  | nil =>
      simp [kmpSearchPositionsAux]
      have hnil : PendingMatches pat pref [] = [] := by
        rw [pendingMatches_eq_Ico_filter (pat := pat) (pref := pref) (txt := ([] : List α))]
        apply List.filter_eq_nil_iff.2
        intro i hi
        by_cases hpre : pat.isPrefixOf ((pref ++ ([] : List α)).drop i) = true
        · exfalso
          have hiLo : pref.length + 1 - pat.length ≤ i := (List.Ico.mem.1 hi).1
          have hiHi : i < pref.length := by
            simpa using (List.Ico.mem.1 hi).2
          have hgt : pref.length < i + pat.length := by
            omega
          have hprefix : pat <+: pref.drop i :=
            (List.isPrefixOf_iff_prefix).1 (by simpa using hpre)
          have hlenPat : pat.length ≤ (pref.drop i).length := hprefix.length_le
          have hle : i + pat.length ≤ pref.length := by
            calc
              i + pat.length ≤ i + (pref.drop i).length := Nat.add_le_add_left hlenPat i
              _ = i + (pref.length - i) := by simp [List.length_drop]
              _ = pref.length := by omega
          exact (Nat.not_lt_of_ge hle) hgt
        · intro hprefix
          exact hpre hprefix
      simpa using hnil.symm
  | cons t ts ih =>
      rw [kmpSearchPositionsAux_eval_cons]
      have hstateStep :
          FrontierState pat (pref ++ [t])
            (match (kmpSearchFallback ((buildLPS pat).eval Comparison.natCost).length t k pat
                ((buildLPS pat).eval Comparison.natCost)).eval Comparison.natCost with
            | none => 0
            | some k' => k' + 1) := by
        exact frontierState_step_kmpSearchFallback_eval
          (hTableLen := hTableLen) (hprefix := hprefix) (hstate := hstate)
          (hkPat := hkPat) (t := t)
      cases hres : (kmpSearchFallback ((buildLPS pat).eval Comparison.natCost).length t k pat
          ((buildLPS pat).eval Comparison.natCost)).eval Comparison.natCost with
      | none =>
          have hstate0 : FrontierState pat (pref ++ [t]) 0 := by
            simpa [hres] using hstateStep
          have hnohit :
              ¬(pat.length ≤ (pref ++ [t]).length ∧
                pat.isPrefixOf
                  ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true) := by
            intro hhit
            rcases (kmpSearchFallback_eval_some_full_iff_match_start
              (hTableLen := hTableLen) (hprefix := hprefix) (hstate := hstate)
              (hkPat := hkPat) (t := t) (ts := ts)).2 hhit with ⟨k', hk'⟩
            rw [hres] at hk'
            cases hk'.1
          rw [pendingMatches_cons (hpat := h0), if_neg hnohit]
          simp
          simpa using ih (pref := pref ++ [t]) (k := 0) h0 hstate0
      | some k' =>
          by_cases hfull : k' + 1 = pat.length
          · have hhit :
              pat.length ≤ (pref ++ [t]).length ∧
                pat.isPrefixOf
                  ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true :=
              (kmpSearchFallback_eval_some_full_iff_match_start
                (hTableLen := hTableLen) (hprefix := hprefix) (hstate := hstate)
                (hkPat := hkPat) (t := t) (ts := ts)).1 ⟨k', hres, hfull⟩
            have hstateFull : FrontierState pat (pref ++ [t]) pat.length := by
              simpa [hres, hfull] using hstateStep
            let reset : Nat :=
              match ((buildLPS pat).eval Comparison.natCost)[pat.length]? with
              | some suffixLen => Int.toNat suffixLen
              | none => 0
            have hresetState : FrontierState pat (pref ++ [t]) reset := by
              dsimp [reset]
              exact frontierState_reset_buildLPS_nonempty (pat := pat) h0 hstateFull
            have hresetLt : reset < pat.length := by
              dsimp [reset]
              simpa using (hbuildSpec h0).2.2.2
            rw [pendingMatches_cons (hpat := h0), if_pos hhit]
            dsimp [reset]
            rw [if_pos hfull]
            rw [kmpSearchPositionsAux_eval_append_acc]
            simp
            simpa using ih (pref := pref ++ [t]) (k := reset) hresetLt hresetState
          · have hspecSome :
                FallbackCandidate pat k k' ∧
                  pat[k']? = some t ∧
                  ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
              simpa [hres] using
                (kmpSearchFallback_eval_full_spec
                  (pat := pat) (table := (buildLPS pat).eval Comparison.natCost)
                  hTableLen hprefix t hkPat)
            have hk'Pat : k' < pat.length :=
              lt_of_le_of_lt (fallbackCandidate_le hspecSome.1) hkPat
            have hnextLt : k' + 1 < pat.length := by
              omega
            have hstateNext : FrontierState pat (pref ++ [t]) (k' + 1) := by
              simpa [hres, hfull] using hstateStep
            have hnohit :
                ¬(pat.length ≤ (pref ++ [t]).length ∧
                  pat.isPrefixOf
                    ((pref ++ t :: ts).drop ((pref ++ [t]).length - pat.length)) = true) := by
              intro hhit
              rcases (kmpSearchFallback_eval_some_full_iff_match_start
                (hTableLen := hTableLen) (hprefix := hprefix) (hstate := hstate)
                (hkPat := hkPat) (t := t) (ts := ts)).2 hhit with ⟨k'', hk'', hkfull⟩
              rw [hres] at hk''
              cases hk''
              exact hfull hkfull
            rw [pendingMatches_cons (hpat := h0), if_neg hnohit]
            simp [hfull]
            simpa using ih (pref := pref ++ [t]) (k := k' + 1) hnextLt hstateNext

theorem kmpPatternSearch_eval [BEq α] [LawfulBEq α] (pat txt : List α) :
    (kmpSearchPositions pat txt).eval Comparison.natCost = PatternSearchAll pat txt := by
  cases pat with
  | nil =>
      simpa using kmpSearchPositions_eval_nil (txt := txt)
  | cons p ps =>
      have hPending :
          PendingMatches (p :: ps) [] txt = PatternSearchAll (p :: ps) txt := by
        unfold PendingMatches
        apply List.filter_eq_self.2
        intro i hi
        simp
      have hFrontierNil : FrontierState (p :: ps) [] 0 := by
        refine ⟨by simp, by simp, ?_⟩
        intro l _ hl0 _
        simpa using hl0
      simp [kmpSearchPositions, Prog.eval_bind]
      simpa [hPending]
        using
          (kmpSearchPositionsAux_eval_pendingMatches
            (pat := p :: ps) (pref := []) (txt := txt) (k := 0)
            (by simp) (by simp) hFrontierNil)

section SearchTimeComplexity

private def fallbackPotential : Option Nat → Nat
  | none => 0
  | some k' => k' + 1

private lemma kmpSearchFallback_time_potential_upper_bound [BEq α] [LawfulBEq α]
    {pat : List α} {table : List Int}
    (hTableLen : table.length = pat.length + 1)
    (hprefix : FailurePrefix pat table pat.length (by omega) hTableLen)
    (t : α) :
    ∀ (fuel k : Nat), (hk : k < pat.length) → k + 1 ≤ fuel →
      (kmpSearchFallback fuel t k pat table).time Comparison.natCost +
        fallbackPotential ((kmpSearchFallback fuel t k pat table).eval Comparison.natCost)
      ≤ k + 2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk hFuel
      omega
  | succ fuel ih =>
      intro k hk hFuel
      cases hpk : pat[k]? with
      | none =>
          exfalso
          have hpkSome : pat[k]? = some (pat[k]'hk) := by
            exact List.getElem?_eq_getElem (l := pat) (i := k) hk
          simp [hpk] at hpkSome
      | some pk =>
          by_cases hcmp : pk == t
          · simp [kmpSearchFallback, hpk, hcmp, fallbackPotential]
            omega
          · have hkTable : k < table.length := by omega
            cases hnext : table[k]? with
            | none =>
                exfalso
                have hnextSome : table[k]? = some (table[k]'hkTable) := by
                  exact List.getElem?_eq_getElem (l := table) (i := k) hkTable
                simp [hnext] at hnextSome
            | some nextK =>
                by_cases hneg : nextK < 0
                · simp [kmpSearchFallback, hpk, hcmp, hnext, hneg, fallbackPotential]
                · have hnonneg : 0 ≤ nextK := by omega
                  have hEntry : FailureEntry pat k hk nextK :=
                    failureEntry_of_table_get? hTableLen hprefix hk hnext
                  have hkNextLtK : Int.toNat nextK < k :=
                    failureEntry_target_lt hEntry hnonneg
                  have hkNext : Int.toNat nextK < pat.length := lt_trans hkNextLtK hk
                  have hFuelNext : Int.toNat nextK + 1 ≤ fuel := by omega
                  have hrec := ih (Int.toNat nextK) hkNext hFuelNext
                  have hstep :
                      (kmpSearchFallback (fuel + 1) t k pat table).time Comparison.natCost +
                        fallbackPotential
                          ((kmpSearchFallback (fuel + 1) t k pat table).eval
                            Comparison.natCost)
                        =
                      1 + ((kmpSearchFallback fuel t (Int.toNat nextK) pat table).time
                            Comparison.natCost +
                          fallbackPotential
                            ((kmpSearchFallback fuel t (Int.toNat nextK) pat table).eval
                              Comparison.natCost)) := by
                    simp [kmpSearchFallback, hpk, hcmp, hnext, hneg, fallbackPotential,
                      Nat.add_assoc]
                  rw [hstep]
                  omega

private lemma kmpSearchPositionsAux_time_linear_buildLPS [BEq α] [LawfulBEq α]
    {pat txt : List α} (h0 : 0 < pat.length)
    {j k : Nat} (hk : k < pat.length) (accRev : List Nat) :
    (kmpSearchPositionsAux txt j k pat ((buildLPS pat).eval Comparison.natCost) accRev).time
      Comparison.natCost ≤ 2 * txt.length + k := by
  rcases buildLPS_spec (pat := pat) with ⟨hTableLen, hprefix, hbuildSpec⟩
  set table : List Int := (buildLPS pat).eval Comparison.natCost
  have hTableLen' : table.length = pat.length + 1 := by
    simpa [table] using hTableLen
  have hprefix' : FailurePrefix pat table pat.length (by omega) hTableLen' := by
    simpa [table] using hprefix
  have hresetLt :
      (match table[pat.length]? with
      | some suffixLen => Int.toNat suffixLen
      | none => 0) < pat.length := by
    simpa [table] using (hbuildSpec h0).2.2.2
  induction txt generalizing j k accRev with
  | nil =>
      simp [kmpSearchPositionsAux]
  | cons t ts ih =>
      set fallback : Prog (Comparison α) (Option Nat) :=
        kmpSearchFallback table.length t k pat table
      have hFallback :
          fallback.time Comparison.natCost +
              fallbackPotential (fallback.eval Comparison.natCost) ≤ k + 2 := by
        simpa [fallback] using
          (kmpSearchFallback_time_potential_upper_bound
            (pat := pat) (table := table) hTableLen' hprefix' t table.length k hk (by omega))
      cases hres : fallback.eval Comparison.natCost with
      | none =>
          have hFallbackTime : fallback.time Comparison.natCost ≤ k + 2 := by
            simpa [fallbackPotential, hres] using hFallback
          have hrec :=
            ih (j := j + 1) (k := 0) (by simpa using h0) (accRev := accRev) hprefix'
          have htime :
              (kmpSearchPositionsAux (t :: ts) j k pat table accRev).time
                  Comparison.natCost =
                fallback.time Comparison.natCost +
                  (kmpSearchPositionsAux ts (j + 1) 0 pat table accRev).time
                    Comparison.natCost := by
            simp [kmpSearchPositionsAux, Prog.time_bind, fallback, hres]
          rw [htime]
          have hsum :
              fallback.time Comparison.natCost +
                  (kmpSearchPositionsAux ts (j + 1) 0 pat table accRev).time
                    Comparison.natCost ≤
                (k + 2) + (2 * ts.length) :=
            Nat.add_le_add hFallbackTime (by simpa using hrec)
          calc
            fallback.time Comparison.natCost +
                (kmpSearchPositionsAux ts (j + 1) 0 pat table accRev).time
                  Comparison.natCost ≤
              (k + 2) + (2 * ts.length) := hsum
            _ = 2 * (t :: ts).length + k := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]
      | some k' =>
          have hspec :
              FallbackCandidate pat k k' ∧
                pat[k']? = some t ∧
                ∀ l, FallbackCandidate pat k l → pat[l]? = some t → l ≤ k' := by
            simpa [fallback, hres] using
              (kmpSearchFallback_eval_full_spec
                (pat := pat) (table := table) hTableLen' hprefix' t hk)
          have hk'Pat : k' < pat.length := (List.getElem?_eq_some_iff.mp hspec.2.1).1
          have hFallbackSome : fallback.time Comparison.natCost + (k' + 1) ≤ k + 2 := by
            simpa [fallbackPotential, hres] using hFallback
          by_cases hfull : k' + 1 = pat.length
          · let reset : Nat :=
              match table[pat.length]? with
              | some suffixLen => Int.toNat suffixLen
              | none => 0
            have hresetLt' : reset < pat.length := by
              dsimp [reset]
              simpa using hresetLt
            have hrec :=
              ih (j := j + 1) (k := reset) hresetLt'
                (accRev := (j + 1 - pat.length) :: accRev) hprefix'
            have htime :
                (kmpSearchPositionsAux (t :: ts) j k pat table accRev).time
                    Comparison.natCost =
                  fallback.time Comparison.natCost +
                    (kmpSearchPositionsAux ts (j + 1) reset pat table
                      ((j + 1 - pat.length) :: accRev)).time Comparison.natCost := by
              simp [kmpSearchPositionsAux, Prog.time_bind, fallback, hres, hfull, reset]
            rw [htime]
            have hresetLe : reset ≤ k' + 1 := by
              dsimp [reset]
              omega
            have hFallbackReset : fallback.time Comparison.natCost + reset ≤ k + 2 := by
              calc
                fallback.time Comparison.natCost + reset ≤
                    fallback.time Comparison.natCost + (k' + 1) :=
                  Nat.add_le_add_left hresetLe _
                _ ≤ k + 2 := hFallbackSome
            have hsum :
                fallback.time Comparison.natCost +
                    (kmpSearchPositionsAux ts (j + 1) reset pat table
                      ((j + 1 - pat.length) :: accRev)).time Comparison.natCost ≤
                  fallback.time Comparison.natCost + (2 * ts.length + reset) :=
              Nat.add_le_add_left hrec _
            calc
              fallback.time Comparison.natCost +
                  (kmpSearchPositionsAux ts (j + 1) reset pat table
                    ((j + 1 - pat.length) :: accRev)).time Comparison.natCost ≤
                fallback.time Comparison.natCost + (2 * ts.length + reset) := hsum
              _ = 2 * ts.length + (fallback.time Comparison.natCost + reset) := by omega
              _ ≤ 2 * ts.length + (k + 2) := Nat.add_le_add_left hFallbackReset _
              _ = 2 * (t :: ts).length + k := by
                simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]
          · have hkNext : k' + 1 < pat.length := by omega
            have hrec :=
              ih (j := j + 1) (k := k' + 1) hkNext (accRev := accRev) hprefix'
            have htime :
                (kmpSearchPositionsAux (t :: ts) j k pat table accRev).time
                    Comparison.natCost =
                  fallback.time Comparison.natCost +
                    (kmpSearchPositionsAux ts (j + 1) (k' + 1) pat table accRev).time
                      Comparison.natCost := by
              simp [kmpSearchPositionsAux, Prog.time_bind, fallback, hres, hfull]
            rw [htime]
            have hsum :
                fallback.time Comparison.natCost +
                    (kmpSearchPositionsAux ts (j + 1) (k' + 1) pat table accRev).time
                      Comparison.natCost ≤
                  fallback.time Comparison.natCost + (2 * ts.length + (k' + 1)) :=
              Nat.add_le_add_left hrec _
            calc
              fallback.time Comparison.natCost +
                  (kmpSearchPositionsAux ts (j + 1) (k' + 1) pat table accRev).time
                    Comparison.natCost ≤
                fallback.time Comparison.natCost + (2 * ts.length + (k' + 1)) := hsum
              _ = 2 * ts.length + (fallback.time Comparison.natCost + (k' + 1)) := by omega
              _ ≤ 2 * ts.length + (k + 2) := Nat.add_le_add_left hFallbackSome _
              _ = 2 * (t :: ts).length + k := by
                simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem kmpSearchPositions_time_complexity_upper_bound [BEq α] [LawfulBEq α]
    (pat txt : List α) :
    (kmpSearchPositions pat txt).time Comparison.natCost ≤
      2 * txt.length + 2 * (pat.length - 1) := by
  cases pat with
  | nil =>
      simp [kmpSearchPositions]
  | cons p ps =>
      have haux :
          (kmpSearchPositionsAux txt 0 0 (p :: ps)
            ((buildLPS (p :: ps)).eval Comparison.natCost) []).time
              Comparison.natCost ≤ 2 * txt.length := by
        simpa using
          (kmpSearchPositionsAux_time_linear_buildLPS
            (pat := p :: ps) (txt := txt) (h0 := by simp)
            (j := 0) (k := 0) (hk := by simp) (accRev := []))
      have hbuild := buildLPS_time_complexity_upper_bound (pat := p :: ps)
      have htime :
          (kmpSearchPositions (p :: ps) txt).time Comparison.natCost =
            (buildLPS (p :: ps)).time Comparison.natCost +
              (kmpSearchPositionsAux txt 0 0 (p :: ps)
                ((buildLPS (p :: ps)).eval Comparison.natCost) []).time
                  Comparison.natCost := by
        simp [kmpSearchPositions, Prog.time_bind]
      rw [htime]
      omega

end SearchTimeComplexity

end Correctness

end Algorithms

end Cslib
