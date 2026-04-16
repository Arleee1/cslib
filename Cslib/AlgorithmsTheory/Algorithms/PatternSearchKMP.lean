/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.Models.Comparison
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Infix

@[expose] public section

/-!
# Knuth-Morris-Pratt preprocessing

In this file we define the longest-proper-prefix / suffix table used by KMP in the
`Comparison` query model.
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
        have hnextPat : Int.toNat nextCnd < pat.length := by
          exact htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat nextCnd < table.length := by
          calc
            Int.toNat nextCnd < pat.length := hnextPat
            _ < pat.length + 1 := Nat.lt_succ_self _
            _ = table.length := htableLen.symm
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
          innerLPSWhile table.length pos cnd pat table hpos hcndPat hcndTable htableLen htableBound
      let entry : Int :=
        if cmp then
          table[(Int.toNat cnd)]'hcndTable
        else
          cnd
      let table' := table.set pos entry
      let nextCnd := fallbackCnd + 1
      have hposTable : pos < table.length := by
        calc
          pos < pat.length := hpos
          _ < pat.length + 1 := Nat.lt_succ_self _
          _ = table.length := htableLen.symm
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
        · have hNe : pos ≠ i := by
            exact fun h => hEq h.symm
          have hget : table'[i] = table[i]'(by simpa [table'] using hi) := by
            simpa only [table'] using List.getElem_set_of_ne hNe entry hi
          rw [hget]
          exact htableBound i (by simpa only [List.length_set, table'] using hi)
      if hnextPos : pos + 1 < pat.length then
        if hnextCndPat : Int.toNat nextCnd < pat.length then
          have hnextCndTable : Int.toNat nextCnd < table'.length := by
            calc
              Int.toNat nextCnd < pat.length := hnextCndPat
              _ < pat.length + 1 := Nat.lt_succ_self _
              _ = table'.length := htableLen'.symm
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
        LPSWhile (x :: y :: xs).length 1 0 (x :: y :: xs) table0
          hpos hcndPat hcndTable htableLen htableBound
      let table' := table.set (x :: y :: xs).length cnd
      return table'

section TimeComplexity


private lemma int_toNat_add_one_eq {z : Int} (hz : 0 ≤ z) :
    Int.toNat (z + 1) = Int.toNat z + 1 := by
  apply Int.ofNat.inj
  simp
  omega

private lemma int_toNat_add_one_le_of_ge_neg_one {z : Int} (hz : -1 ≤ z) :
    Int.toNat (z + 1) ≤ Int.toNat z + 1 := by
  by_cases hnonneg : 0 ≤ z
  · rw [int_toNat_add_one_eq hnonneg]
  · have hz' : z = -1 := by omega
    subst hz'
    decide

private lemma innerLPSWhile_eval_lower_bound [BEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (hcndTable : Int.toNat cnd < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length)
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (hcndLower : -1 ≤ cnd) :
    -1 ≤ (innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval
      Comparison.natCost := by
  induction fuel generalizing pos cnd with
  | zero =>
      simpa [innerLPSWhile, Prog.eval] using hcndLower
  | succ fuel ih =>
      by_cases hcndNeg : cnd < 0
      · simpa [innerLPSWhile, Prog.eval, hcndNeg] using hcndLower
      · have hnextPat : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < pat.length :=
          htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < table.length := by
          omega
        have hnextLower : -1 ≤ table[(Int.toNat cnd)]'hcndTable :=
          htableLower (Int.toNat cnd) hcndTable
        by_cases hcmp : pat[pos]'hpos == pat[(Int.toNat cnd)]'hcndPat
        · simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using hcndLower
        · simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp] using
            ih pos (table[(Int.toNat cnd)]'hcndTable) hpos hnextPat hnextTable hnextLower

private lemma innerLPSWhile_eval_add_one_upper_bound [BEq α]
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
    Int.toNat ((innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).eval
      Comparison.natCost + 1) ≤ Int.toNat cnd + 1 := by
  induction fuel generalizing pos cnd with
  | zero =>
      simp [innerLPSWhile, Prog.eval]
  | succ fuel ih =>
      by_cases hcndNeg : cnd < 0
      · simp [innerLPSWhile, Prog.eval, hcndNeg]
      · have hnextPat : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < pat.length :=
          htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < table.length := by
          omega
        have hnextLower : -1 ≤ table[(Int.toNat cnd)]'hcndTable :=
          htableLower (Int.toNat cnd) hcndTable
        by_cases hcmp : pat[pos]'hpos == pat[(Int.toNat cnd)]'hcndPat
        · simp [innerLPSWhile, Prog.eval, hcndNeg, hcmp]
        · have hstep := htableStep (Int.toNat cnd) hcndTable
          have hrec := ih pos (table[(Int.toNat cnd)]'hcndTable) hpos hnextPat
            hnextTable hnextLower
          simp [Prog.eval] at hrec
          simp [innerLPSWhile, Prog.eval, hcndNeg, hcmp]
          omega

private lemma innerLPSWhile_time_eval_upper_bound [BEq α]
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
    (innerLPSWhile fuel pos cnd pat table
      hpos hcndPat hcndTable htableLen htableBound).time
      Comparison.natCost +
      Int.toNat ((innerLPSWhile fuel pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound).eval
        Comparison.natCost + 1) ≤ Int.toNat cnd + 2 := by
  induction fuel generalizing pos cnd with
  | zero =>
      simp [innerLPSWhile, Prog.eval]
      omega
  | succ fuel ih =>
      by_cases hcndNeg : cnd < 0
      · have hcndEq : cnd = -1 := by omega
        subst hcndEq
        simp [innerLPSWhile, Prog.eval]
      · have hnextPat : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < pat.length :=
          htableBound (Int.toNat cnd) hcndTable
        have hnextTable : Int.toNat (table[(Int.toNat cnd)]'hcndTable) < table.length := by
          omega
        have hnextLower : -1 ≤ table[(Int.toNat cnd)]'hcndTable :=
          htableLower (Int.toNat cnd) hcndTable
        by_cases hcmp : pat[pos]'hpos == pat[(Int.toNat cnd)]'hcndPat
        · simp [innerLPSWhile, Prog.eval, hcndNeg, hcmp]
          omega
        · have hstep := htableStep (Int.toNat cnd) hcndTable
          by_cases hnextNeg : table[(Int.toNat cnd)]'hcndTable < 0
          · have hnextEq : table[(Int.toNat cnd)]'hcndTable = -1 := by omega
            have hnextPat' : Int.toNat (-1 : Int) < pat.length := by
              simpa [hnextEq] using hnextPat
            have hnextTable' : Int.toNat (-1 : Int) < table.length := by
              simpa [hnextEq] using hnextTable
            have hinnerZero :
                (innerLPSWhile fuel pos (table[(Int.toNat cnd)]'hcndTable) pat table
                  hpos hnextPat hnextTable htableLen htableBound).time
                  Comparison.natCost +
                Int.toNat
                  ((innerLPSWhile fuel pos (table[(Int.toNat cnd)]'hcndTable) pat table
                    hpos hnextPat hnextTable htableLen htableBound).eval
                    Comparison.natCost + 1) = 0 := by
              simpa [hnextEq] using
                (show (innerLPSWhile fuel pos (-1) pat table
                    hpos hnextPat' hnextTable' htableLen htableBound).time
                    Comparison.natCost +
                  Int.toNat
                    ((innerLPSWhile fuel pos (-1) pat table
                      hpos hnextPat' hnextTable' htableLen htableBound).eval
                      Comparison.natCost + 1) = 0 by
                  cases fuel <;> simp [innerLPSWhile, Prog.eval, Prog.time])
            simp [innerLPSWhile, Prog.eval, Prog.time, hcndNeg, hcmp, hnextEq] at hinnerZero ⊢
            omega
          · have hnextNonneg : 0 ≤ table[(Int.toNat cnd)]'hcndTable := by omega
            have hstep' :
                Int.toNat (table[(Int.toNat cnd)]'hcndTable) + 1 ≤ Int.toNat cnd := by
              rw [← int_toNat_add_one_eq hnextNonneg]
              exact hstep
            have hrec := ih pos (table[(Int.toNat cnd)]'hcndTable) hpos hnextPat
              hnextTable hnextLower
            simp [Prog.eval] at hrec
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
  · subst heq
    simpa only [List.getElem_set_self] using hv
  · rw [List.getElem_set_of_ne (by omega)]; exact htableBound i (by omega)

/-- Helper: `List.set` preserves lower bounds. -/
private lemma table_set_lower {table : List Int} {pos : Nat} {v : Int}
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (hv : -1 ≤ v)
    (i : Nat) (hi : i < (table.set pos v).length) :
    -1 ≤ (table.set pos v)[i]'hi := by
  simp only [List.length_set] at hi
  by_cases heq : i = pos
  · subst heq
    simpa only [List.getElem_set_self] using hv
  · rw [List.getElem_set_of_ne (by omega)]; exact htableLower i (by omega)

/-- Helper: `List.set` preserves the step invariant. -/
private lemma table_set_step {table : List Int} {pos : Nat} {v : Int}
    (htableStep : ∀ (i : Nat) (hi : i < table.length), Int.toNat (table[i]'hi + 1) ≤ i)
    (hv : Int.toNat (v + 1) ≤ pos)
    (i : Nat) (hi : i < (table.set pos v).length) :
    Int.toNat ((table.set pos v)[i]'hi + 1) ≤ i := by
  simp only [List.length_set] at hi
  by_cases heq : i = pos
  · subst heq
    simpa only [List.getElem_set_self] using hv
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
      Comparison.natCost ≤ 3 * fuel + Int.toNat cnd + 1 := by
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
    have hcndLePos : Int.toNat cnd ≤ pos := by
      rw [hcndSucc] at hcndStep
      omega
    split_ifs with hcmp hpos' hcndPat'
    · -- cmp = true, pos + 1 < pat.length, nextCnd in range: recurse
      have hentryStep : Int.toNat (table[(Int.toNat cnd)]'hcndTable + 1) ≤ pos := by
        exact le_trans (htableStep (Int.toNat cnd) hcndTable) hcndLePos
      have hrec := ih (pos + 1) (cnd + 1) (table.set pos table[cnd.toNat]) hpos' hcndPat'
        (by simp [List.length_set]; omega) (by rw [List.length_set, htableLen])
        (table_set_bound htableBound (htableBound _ hcndTable) hposTable)
        (by omega) (by rw [int_toNat_add_one_eq (by omega), hcndSucc]; omega)
        (table_set_lower htableLower (htableLower _ hcndTable))
        (table_set_step htableStep hentryStep)
      omega
    · simp [Prog.time_pure]
    · simp [Prog.time_pure]
    · -- cmp = false, pos + 1 < pat.length: inner loop + possible recurse
      rename_i hpos_next
      rw [Prog.time_bind]
      set inner : Prog (Comparison α) Int :=
        innerLPSWhile table.length pos cnd pat table
          hpos hcndPat hcndTable htableLen htableBound
      have hinnerLower := innerLPSWhile_eval_lower_bound
        table.length pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound htableLower (by omega)
      have hinnerEval := innerLPSWhile_eval_add_one_upper_bound
        table.length pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound htableLower htableStep (by omega)
      have hinner := innerLPSWhile_time_eval_upper_bound
        table.length pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound htableLower htableStep (by omega)
      have hnextNonneg : 0 ≤ inner.eval Comparison.natCost + 1 := by
        have hinnerLower' : -1 ≤ inner.eval Comparison.natCost := by
          simpa [inner] using hinnerLower
        omega
      have hnextEval : Int.toNat (inner.eval Comparison.natCost + 1) ≤ Int.toNat cnd + 1 := by
        simpa [inner] using hinnerEval
      have hinner' :
          inner.time Comparison.natCost +
            Int.toNat (inner.eval Comparison.natCost + 1) ≤ Int.toNat cnd + 2 := by
        simpa [inner] using hinner
      split_ifs with hcndPat_rec
      · have hnextStep : Int.toNat ((inner.eval Comparison.natCost + 1) + 1) ≤ pos + 1 := by
          rw [int_toNat_add_one_eq hnextNonneg]
          omega
        have hrec := ih (pos + 1) (inner.eval Comparison.natCost + 1)
          (table.set pos cnd) hpos_next hcndPat_rec
          (by simp [List.length_set]; omega) (by rw [List.length_set, htableLen])
          (table_set_bound htableBound hcndPat hposTable) hnextNonneg hnextStep
          (table_set_lower htableLower (by omega))
          (table_set_step htableStep hcndStep)
        omega
      · rw [Prog.time_pure]
        simp
        omega
    · -- cmp = false, ¬(pos + 1 < pat.length)
      rw [Prog.time_bind, Prog.time_pure]
      have hinner := innerLPSWhile_time_eval_upper_bound
        table.length pos cnd pat table
        hpos hcndPat hcndTable htableLen htableBound htableLower htableStep (by omega)
      simp at hinner ⊢
      omega

theorem buildLPS_time_complexity_upper_bound [BEq α]
    (pat : List α) :
    (buildLPS pat).time Comparison.natCost ≤
      3 * pat.length + 1 := by
  rcases pat with (_ | ⟨x, _ | ⟨y, xs⟩⟩) <;> simp_all +decide [buildLPS]
  have htime := LPSWhile_time_complexity_upper_bound (x :: y :: xs).length 1 0
    (x :: y :: xs) (-1 :: List.replicate (List.length (x :: y :: xs)) 0)
    (by simp) (by simp) (by simp) (by simp)
    (by intro i hi; cases i <;> simp)
    (by omega) (by simp)
    (by intro i hi; cases i <;> simp)
    (by intro i hi; cases i <;> simp)
  grind

end TimeComplexity

end Algorithms

end Cslib
