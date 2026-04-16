/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Cslib.AlgorithmsTheory.Models.Comparison
public import Cslib.AlgorithmsTheory.Algorithms.PatternSearchNaive
public import Mathlib.Algebra.Order.Group.Nat
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
          let nextCnd := table[(Int.toNat cnd)]'hcndTable
          have hnextPat : Int.toNat nextCnd < pat.length := by
            exact htableBound (Int.toNat cnd) hcndTable
          have hnextTable : Int.toNat nextCnd < table.length := by
            calc
              Int.toNat nextCnd < pat.length := hnextPat
              _ < pat.length + 1 := Nat.lt_succ_self _
              _ = table.length := htableLen.symm
          innerLPSWhile table.length pos nextCnd pat table
            hpos hnextPat hnextTable htableLen htableBound
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



section Correctness

private def Border (pat : List α) (n l : Nat) : Prop :=
  l < n ∧ pat.take l = (pat.take n).drop (n - l)

private def LongestBorder (pat : List α) (n l : Nat) : Prop :=
  Border pat n l ∧ ∀ l', Border pat n l' → l' ≤ l

private def FailureEntry [BEq α] (pat : List α) (k : Nat) (hk : k < pat.length) (v : Int) : Prop :=
  if hneg : v < 0 then
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

private lemma border_zero {pat : List α} {n : Nat} (hn : 0 < n) : Border pat n 0 := by
  constructor
  · simpa using hn
  · simp

private lemma border_trans {pat : List α} {n c l : Nat}
    (hcn : Border pat n c) (hlc : Border pat c l) : Border pat n l := by
  rcases hcn with ⟨hcnlt, hcn⟩
  rcases hlc with ⟨hlclt, hlc⟩
  constructor
  · omega
  · rw [hlc, hcn]
    rw [List.drop_drop]
    congr
    omega

private lemma border_of_longest_prefix {pat : List α} {n c l : Nat}
    (hcn : Border pat n c) (hl : Border pat n l) (hlt : l < c) : Border pat c l := by
  rcases hcn with ⟨_, hcn⟩
  rcases hl with ⟨_, hl⟩
  constructor
  · exact hlt
  · rw [hcn]
    rw [List.drop_drop]
    have : n - c + (c - l) = n - l := by omega
    simp [this]
    exact hl

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
  constructor
  · exact border_extend hn hl hlBorder hcmp
  · intro l' hl'
    cases l' with
    | zero =>
        omega
    | succ l'' =>
        have hl'' : l'' < pat.length := by
          have : l'' + 1 < n + 1 := hl'.1
          omega
        have hprev := border_prev hn hl'' hl'
        have hle : l'' ≤ l := hlMax l'' hprev.1
        omega

private lemma bestMatchingBorder_to_longest [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hbest : BestMatchingBorder pat n hn l) :
    LongestBorder pat (n + 1) (l + 1) := by
  rcases hbest with ⟨hlBorder, hcmp, hlMax⟩
  constructor
  · exact border_extend hn hl hlBorder hcmp
  · intro l' hl'
    cases l' with
    | zero =>
        omega
    | succ l'' =>
        have hl'' : l'' < pat.length := by
          have : l'' + 1 < n + 1 := hl'.1
          omega
        have hprev := border_prev hn hl'' hl'
        have hle : l'' ≤ l := hlMax l'' hprev.1 hprev.2
        omega

private lemma no_matching_border_to_longest_zero [BEq α] {pat : List α} {n : Nat}
    (hn : n < pat.length)
    (hnone : ∀ l, (hl : Border pat n l) →
      pat[n]'hn ≠ pat[l]'(lt_trans hl.1 hn)) :
    LongestBorder pat (n + 1) 0 := by
  constructor
  · exact border_zero (Nat.succ_pos _)
  · intro l' hl'
    cases l' with
    | zero =>
        omega
    | succ l'' =>
        have hl'' : l'' < pat.length := by
          have : l'' + 1 < n + 1 := hl'.1
          omega
        have hprev := border_prev hn hl'' hl'
        exact False.elim (hnone l'' hprev.1 hprev.2)

private lemma failure_transfer_of_eq [BEq α] {pat : List α} {pos c : Nat} {v : Int}
    (hpos : pos < pat.length) (hc : c < pat.length)
    (hlong : LongestBorder pat pos c)
    (hv : FailureEntry pat c hc v)
    (hcmp : pat[pos]'hpos = pat[c]'hc) :
    FailureEntry pat pos hpos v := by
  rcases hlong with ⟨hcBorder, hcMax⟩
  unfold FailureEntry at hv ⊢
  by_cases hneg : v < 0
  · simp [hneg] at hv ⊢
    intro l hl
    by_cases hlc : l = c
    · simpa [hlc] using hcmp
    · have hle : l ≤ c := hcMax l hl
      have hlt : l < c := by omega
      have hlBorderC : Border pat c l := border_of_longest_prefix hcBorder hl hlt
      have hEq : pat[c]'hc = pat[l]'(lt_trans hlBorderC.1 hc) := hv l hlBorderC
      simpa [hcmp] using hEq
  · have hv' :
        ∃ hn : Border pat c (Int.toNat v),
          pat[c]'hc ≠ pat[Int.toNat v]'(lt_trans hn.1 hc) ∧
          ∀ l, (hl : Border pat c l) →
            pat[c]'hc ≠ pat[l]'(lt_trans hl.1 hc) → l ≤ Int.toNat v := by
        simpa [FailureEntry, hneg] using hv
    rcases hv' with ⟨hnBorder, hvNe, hvMax⟩
    simp [FailureEntry, hneg]
    refine ⟨?_, ?_⟩
    · refine ⟨border_trans hcBorder hnBorder, ?_⟩
      intro hEq
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
  have hcEq : Int.toNat (c : Int) = c := by simp
  unfold FailureEntry
  simp [hnonneg, hcEq]
  refine ⟨⟨hcBorder, hcmp⟩, ?_⟩
  intro l hl _
  exact hcMax l hl

private lemma failureEntry_zero [BEq α] {pat : List α} (h0 : 0 < pat.length) :
    FailureEntry pat 0 h0 (-1) := by
  unfold FailureEntry
  simp
  intro l hl
  exact False.elim (Nat.not_lt_zero _ hl.1)

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
    LongestBorder pat 1 0 := by
  constructor
  · exact border_zero (Nat.succ_pos _)
  · intro l hl
    cases l with
    | zero =>
        exact Nat.zero_le 0
    | succ l =>
        exact False.elim (by
          rcases hl with ⟨hlt, _⟩
          omega)

private lemma longestBorder_to_matchingFrontier {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hlong : LongestBorder pat n l) :
    MatchingFrontier pat n hn l := by
  rcases hlong with ⟨hlBorder, hlMax⟩
  exact ⟨hlBorder, fun l' hl' _ => hlMax l' hl'⟩

private lemma matchingFrontier_to_best [BEq α] {pat : List α} {n l : Nat}
    (hn : n < pat.length) (hl : l < pat.length)
    (hfront : MatchingFrontier pat n hn l)
    (hcmp : pat[n]'hn = pat[l]'hl) :
    BestMatchingBorder pat n hn l := by
  rcases hfront with ⟨hlBorder, hlMax⟩
  refine ⟨hlBorder, ?_, hlMax⟩
  simpa using hcmp

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
          exact hcmp (by simpa [hEq])
        set nextCnd : Int := table[Int.toNat cnd]'hcndTable with hnextEq
        by_cases hnextNeg : nextCnd < 0
        · have hnextPat : Int.toNat nextCnd < pat.length := by
            simpa [hnextEq] using htableBound (Int.toNat cnd) hcndTable
          have hnextTable : Int.toNat nextCnd < table.length := by
            calc
              Int.toNat nextCnd < pat.length := hnextPat
              _ < pat.length + 1 := Nat.lt_succ_self _
              _ = table.length := htableLen.symm
          have hinnerNeg :
              (innerLPSWhile fuel pos nextCnd pat table
                hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost = nextCnd := by
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
          have hnextPat : Int.toNat nextCnd < pat.length := by
            simpa [hnextEq] using htableBound (Int.toNat cnd) hcndTable
          have hnextTable : Int.toNat nextCnd < table.length := by
            calc
              Int.toNat nextCnd < pat.length := hnextPat
              _ < pat.length + 1 := Nat.lt_succ_self _
              _ = table.length := htableLen.symm
          have hnextFuel : Int.toNat nextCnd < fuel := by
            have hlt : Int.toNat nextCnd < Int.toNat cnd := by
              simpa [hnextEq] using failureEntry_target_lt hv hnextNonneg
            omega
          have hfront' : MatchingFrontier pat pos hpos (Int.toNat nextCnd) := by
            exact matchingFrontier_of_failure_pos hpos hfront hcndPat
              (by simpa [hnextEq] using hv) hnextNonneg hMis
          simpa [innerLPSWhile, Prog.eval, hcndNeg, hcmp, hnextEq] using
            ih nextCnd hnextPat hnextTable hnextFuel hnextNonneg hfront'

private def LPSInvariant [BEq α] (pat : List α) (pos : Nat) (cnd : Int) (table : List Int)
    (hpos : pos < pat.length) (hcndPat : Int.toNat cnd < pat.length)
    (htableLen : table.length = pat.length + 1) : Prop :=
  0 ≤ cnd ∧ FailurePrefix pat table pos hpos.le htableLen ∧
    LongestBorder pat pos (Int.toNat cnd)

private lemma initial_LPSInvariant [BEq α] {pat : List α} (h1 : 1 < pat.length) :
    LPSInvariant pat 1 0 (-1 :: List.replicate pat.length 0) h1 (by omega)
      (show (-1 :: List.replicate pat.length 0 : List Int).length = pat.length + 1 by simp) := by
  refine ⟨by simp, ?_, longestBorder_one⟩
  simpa using initial_failurePrefix (show 0 < pat.length by omega)

end Correctness

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

private lemma innerLPSWhile_time_eval_upper_bound_from_table [BEq α]
    (fuel pos : Nat) (cnd : Int) (pat : List α) (table : List Int)
    (hpos : pos < pat.length) (hcndTable : Int.toNat cnd < table.length)
    (htableLen : table.length = pat.length + 1)
    (htableBound : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi) < pat.length)
    (htableLower : ∀ (i : Nat) (hi : i < table.length), -1 ≤ table[i]'hi)
    (htableStep : ∀ (i : Nat) (hi : i < table.length),
      Int.toNat (table[i]'hi + 1) ≤ i) :
    let nextCnd := table[(Int.toNat cnd)]'hcndTable
    (innerLPSWhile fuel pos nextCnd pat table
      hpos
      (htableBound (Int.toNat cnd) hcndTable)
      (by
        calc
          Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
          _ < pat.length + 1 := Nat.lt_succ_self _
          _ = table.length := htableLen.symm)
      htableLen htableBound).time Comparison.natCost +
      Int.toNat
        ((innerLPSWhile fuel pos nextCnd pat table
          hpos
          (htableBound (Int.toNat cnd) hcndTable)
          (by
            calc
              Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
              _ < pat.length + 1 := Nat.lt_succ_self _
              _ = table.length := htableLen.symm)
          htableLen htableBound).eval Comparison.natCost + 1) ≤
      Int.toNat cnd + 1 := by
  let nextCnd := table[(Int.toNat cnd)]'hcndTable
  have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
  have hnextTable : Int.toNat nextCnd < table.length := by
    calc
      Int.toNat nextCnd < pat.length := hnextPat
      _ < pat.length + 1 := Nat.lt_succ_self _
      _ = table.length := htableLen.symm
  have hnextLower : -1 ≤ nextCnd := htableLower (Int.toNat cnd) hcndTable
  have hinner := innerLPSWhile_time_eval_upper_bound
    fuel pos nextCnd pat table
    hpos hnextPat hnextTable htableLen htableBound htableLower htableStep hnextLower
  by_cases hnextNeg : nextCnd < 0
  · have hnextEq : nextCnd = -1 := by omega
    have htimeZero :
        (innerLPSWhile fuel pos nextCnd pat table
          hpos hnextPat hnextTable htableLen htableBound).time Comparison.natCost = 0 := by
      cases fuel <;> simp [innerLPSWhile, Prog.time, hnextEq]
    have hevalZero :
        Int.toNat
          ((innerLPSWhile fuel pos nextCnd pat table
            hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost + 1) = 0 := by
      cases fuel <;> simp [innerLPSWhile, Prog.eval, hnextEq]
    dsimp [nextCnd]
    rw [htimeZero, hevalZero]
    omega
  · have hnextNonneg : 0 ≤ nextCnd := by omega
    have hstep' : Int.toNat nextCnd + 1 ≤ Int.toNat cnd := by
      rw [← int_toNat_add_one_eq hnextNonneg]
      simpa [nextCnd] using htableStep (Int.toNat cnd) hcndTable
    simp [nextCnd] at hinner ⊢
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
    have hcndLePos : Int.toNat cnd ≤ pos := by
      rw [hcndSucc] at hcndStep
      omega
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
      have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
      have hnextTable : Int.toNat nextCnd < table.length := by
        calc
          Int.toNat nextCnd < pat.length := hnextPat
          _ < pat.length + 1 := Nat.lt_succ_self _
          _ = table.length := htableLen.symm
      have hnextLower : -1 ≤ nextCnd := htableLower (Int.toNat cnd) hcndTable
      set inner : Prog (Comparison α) Int :=
        innerLPSWhile table.length pos nextCnd pat table
          hpos hnextPat hnextTable htableLen htableBound
      have hinnerLower := innerLPSWhile_eval_lower_bound
        table.length pos nextCnd pat table
        hpos hnextPat hnextTable htableLen htableBound htableLower hnextLower
      have hnextNonneg : 0 ≤ inner.eval Comparison.natCost + 1 := by
        have hinnerLower' : -1 ≤ inner.eval Comparison.natCost := by
          simpa [inner] using hinnerLower
        omega
      have hinner' :
          inner.time Comparison.natCost +
            Int.toNat (inner.eval Comparison.natCost + 1) ≤ Int.toNat cnd + 1 := by
        simpa [inner, nextCnd] using
          innerLPSWhile_time_eval_upper_bound_from_table
            table.length pos cnd pat table
            hpos hcndTable htableLen htableBound htableLower htableStep
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
      have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
      have hnextTable : Int.toNat nextCnd < table.length := by
        calc
          Int.toNat nextCnd < pat.length := hnextPat
          _ < pat.length + 1 := Nat.lt_succ_self _
          _ = table.length := htableLen.symm
      have hnextLower : -1 ≤ nextCnd := htableLower (Int.toNat cnd) hcndTable
      have hinner :
          (innerLPSWhile table.length pos nextCnd pat table
            hpos hnextPat hnextTable htableLen htableBound).time Comparison.natCost +
            Int.toNat
              ((innerLPSWhile table.length pos nextCnd pat table
                hpos hnextPat hnextTable htableLen htableBound).eval Comparison.natCost + 1) ≤
            Int.toNat cnd + 1 := by
        simpa [nextCnd] using
          innerLPSWhile_time_eval_upper_bound_from_table
            table.length pos cnd pat table
            hpos hcndTable htableLen htableBound htableLower htableStep
      simp [nextCnd] at hinner ⊢
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
          have htableBound :
              ∀ (i : Nat) (hi : i < table0.length),
              Int.toNat (table0[i]'hi) < pat'.length := by
            intro i hi
            cases i <;> simp [pat', table0]
          have htableLower :
              ∀ (i : Nat) (hi : i < table0.length), -1 ≤ table0[i]'hi := by
            intro i hi
            cases i <;> simp [pat', table0]
          have htableStep :
              ∀ (i : Nat) (hi : i < table0.length),
              Int.toNat (table0[i]'hi + 1) ≤ i := by
            intro i hi
            cases i <;> simp [pat', table0]
          have htime :=
            LPSWhile_time_complexity_upper_bound (pat'.length - 1) 1 0 pat' table0
              (by simp [pat'])
              (by simp [pat'])
              (by simp [pat', table0])
              (by simp [pat', table0])
              htableBound
              (by omega)
              (by simp)
              htableLower
              htableStep
          simpa [buildLPS, pat', table0] using htime

end TimeComplexity

section MoreCorrectness

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
    have hnextPat : Int.toNat nextCnd < pat.length := htableBound (Int.toNat cnd) hcndTable
    have hnextTable : Int.toNat nextCnd < table.length := by
      calc
        Int.toNat nextCnd < pat.length := hnextPat
        _ < pat.length + 1 := Nat.lt_succ_self _
        _ = table.length := htableLen.symm
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

private lemma initial_table_lower {pat : List α} :
    ∀ (i : Nat) (hi : i < (-1 :: List.replicate pat.length 0 : List Int).length),
      -1 ≤ (-1 :: List.replicate pat.length 0 : List Int)[i]'hi := by
  intro i hi
  cases i <;> simp

private lemma initial_table_step {pat : List α} :
    ∀ (i : Nat) (hi : i < (-1 :: List.replicate pat.length 0 : List Int).length),
      Int.toNat (((-1 :: List.replicate pat.length 0 : List Int)[i]'hi) + 1) ≤ i := by
  intro i hi
  cases i <;> simp

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
    let nextCnd := lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound + 1
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
    have hentryStep : Int.toNat (table[Int.toNat cnd]'hcndTable + 1) ≤ pos := by
      exact le_trans (htableStep (Int.toNat cnd) hcndTable) hcndLePos
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
      exact hcmp (by simpa [hEq])
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
            simp [innerLPSWhile, Prog.eval, hlenTable, hprevNeg]
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
      have hfrontPrev : MatchingFrontier pat pos hpos (Int.toNat prev) := by
        exact matchingFrontier_of_failure_pos hpos hfront hcndPat hvCur hprevNonneg hMis
      have hinner :
          let r := (innerLPSWhile table.length pos prev pat table
            hpos hprevPat hprevTable htableLen htableBound).eval Comparison.natCost
          (r < 0 → ∀ l, (hl : Border pat pos l) →
            pat[pos]'hpos ≠ pat[l]'(lt_trans hl.1 hpos)) ∧
          (0 ≤ r → BestMatchingBorder pat pos hpos (Int.toNat r)) := by
        exact innerLPSWhile_eval_frontier
          table.length pos prev pat table hpos hprevPat hprevTable hprevTable
          htableLen htableBound hprefix hprevNonneg hfrontPrev
      have hfallbackLower : -1 ≤ fallback := by
        simpa [fallback] using innerLPSWhile_eval_lower_bound
          table.length pos prev pat table
          hpos hprevPat hprevTable htableLen htableBound htableLower hprevLower
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
        have hfallbackPat : Int.toNat fallback < pat.length := by
          exact lt_trans hl.1 hpos
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

end MoreCorrectness

section FinalCorrectness

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
  induction fuel generalizing pos cnd table with
  | zero =>
      omega
  | succ fuel ih =>
      rcases lpsStep_invariant pos cnd pat table hpos hcndPat hcndTable htableLen htableBound
        hcndNonneg hcndStep hprefix hlong htableLower htableStep with
        ⟨hlen, hprefix', hbound', hlower', hstep', hnextNonneg, hlong'⟩
      have hremain' : pos + 1 + fuel = pat.length := by omega
      by_cases hnextPos : pos + 1 < pat.length
      · have hnextCndPat :
            Int.toNat
              (lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound + 1) <
              pat.length := by
          exact lt_trans hlong'.1.1 hnextPos
        have hnextCndTable :
            Int.toNat
              (lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound + 1) <
              (table.set pos (lpsStepEntry pos cnd pat table hpos hcndPat hcndTable)).length := by
          calc
            Int.toNat
                (lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound +
                  1) <
                pat.length := hnextCndPat
            _ < pat.length + 1 := Nat.lt_succ_self _
            _ = (table.set pos (lpsStepEntry pos cnd pat table hpos hcndPat hcndTable)).length := by
              simpa using hlen.symm
        have hnextStep :
            Int.toNat
                (lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound +
                    1 + 1) ≤
              pos + 1 := by
          rw [int_toNat_add_one_eq hnextNonneg]
          omega
        have hrec := ih (pos + 1)
          (lpsStepFallback pos cnd pat table hpos hcndPat hcndTable htableLen htableBound + 1)
          (table.set pos (lpsStepEntry pos cnd pat table hpos hcndPat hcndTable))
          hnextPos hnextCndPat hnextCndTable hlen hbound'
          hnextNonneg hnextStep hprefix' hlong' hlower' hstep' hremain'
        simpa [LPSWhile, Prog.eval, lpsStepEntry, lpsStepFallback, hnextPos, hnextCndPat] using hrec
      · have hEq : pos + 1 = pat.length := by omega
        refine ⟨hlen, ?_, hnextNonneg, ?_⟩
        · simpa [hEq] using hprefix'
        · simpa [hEq] using hlong'

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
          have htableBound :
              ∀ (i : Nat) (hi : i < table0.length), Int.toNat (table0[i]'hi) < pat'.length := by
            intro i hi
            cases i <;> simp [pat', table0]
          have htableLower :
              ∀ (i : Nat) (hi : i < table0.length), -1 ≤ table0[i]'hi := by
            intro i hi
            cases i <;> simp [pat', table0]
          have htableStep :
              ∀ (i : Nat) (hi : i < table0.length), Int.toNat (table0[i]'hi + 1) ≤ i := by
            intro i hi
            cases i <;> simp [pat', table0]
          have hinit : FailurePrefix pat' table0 1 hpos.le htableLen := by
            simpa [pat', table0] using initial_failurePrefix (pat := pat') (show 0 < pat'.length by simp [pat'])
          have hfinal := LPSWhile_final (ys.length + 1) 1 0 pat' table0
            hpos hcndPat hcndTable htableLen htableBound
            (by omega) (by simp) hinit longestBorder_one htableLower htableStep (by simp [pat'])
          rcases hfinal with ⟨hlen, hprefix, _, _⟩
          refine ⟨?_, ?_⟩
          · simp [buildLPS, pat', hlen]
          · intro i hi
            have hi' : i < pat'.length := by simpa [pat'] using hi
            have hiGet :
                (((LPSWhile (ys.length + 1) 1 0 pat' table0 hpos hcndPat hcndTable htableLen
                    htableBound).eval Comparison.natCost).fst.set pat'.length
                    ((LPSWhile (ys.length + 1) 1 0 pat' table0 hpos hcndPat hcndTable htableLen
                      htableBound).eval Comparison.natCost).snd)[i]'(by
                        simpa [buildLPS, pat', hlen] using hi) =
                  ((LPSWhile (ys.length + 1) 1 0 pat' table0 hpos hcndPat hcndTable htableLen
                    htableBound).eval Comparison.natCost).fst[i]'(by
                      have : i < ((LPSWhile (ys.length + 1) 1 0 pat' table0 hpos hcndPat hcndTable
                        htableLen htableBound).eval Comparison.natCost).fst.length := by
                        simpa [hlen] using hi
                      exact this) := by
              apply List.getElem_set_of_ne
              omega
            simpa [buildLPS, pat', hiGet, hlen] using hprefix i hi'

end FinalCorrectness

end Algorithms

end Cslib
