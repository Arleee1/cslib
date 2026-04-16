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

end TimeComplexity

end Algorithms

end Cslib
