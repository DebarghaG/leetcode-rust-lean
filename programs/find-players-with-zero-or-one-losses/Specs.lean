import Aegis.FindWinners.Code.Funs

/-!
# Specifications of `Aegis.FindWinners.find_winners`

LeetCode problem `find-players-with-zero-or-one-losses`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindWinners

def matchMatrix («matches» : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  «matches».val.map (fun v => v.val.map (fun x => x.val))

def answerMatrix (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
  r.val.map (fun v => v.val.map (fun x => x.val))

def answerRow (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (b : Nat) : List Int :=
  (answerMatrix r).getD b []

def winnerAt (m : List (List Int)) (i : Nat) : Option Int :=
  (m[i]?).bind (fun row => row[0]?)

def loserAt (m : List (List Int)) (i : Nat) : Option Int :=
  (m[i]?).bind (fun row => row[1]?)

def OccursIn (p : Int) (xs : List Int) : Prop :=
  ∃ t, t < xs.length ∧ xs[t]? = some p

def OccursInMatches (p : Int) (m : List (List Int)) : Prop :=
  ∃ i, i < m.length ∧ (winnerAt m i = some p ∨ loserAt m i = some p)

def NoLoss (p : Int) (m : List (List Int)) : Prop :=
  ¬ ∃ j, j < m.length ∧ loserAt m j = some p

def OneLoss (p : Int) (m : List (List Int)) : Prop :=
  ∃! j, j < m.length ∧ loserAt m j = some p

def AtLeastTwoLosses (p : Int) (m : List (List Int)) : Prop :=
  ∃ j1 j2, j1 < m.length ∧ j2 < m.length ∧ j1 ≠ j2 ∧
    loserAt m j1 = some p ∧ loserAt m j2 = some p

def StrictlyIncreasing (xs : List Int) : Prop :=
  ∀ (j k : Nat) (hjk : j < k) (hk : k < xs.length), xs[j] < xs[k]

def LenBounds (m : List (List Int)) : Prop :=
  1 ≤ m.length ∧ m.length ≤ 100000

def RowsLen2 (m : List (List Int)) : Prop :=
  ∀ e ∈ m, e.length = 2

def EntriesInRange (m : List (List Int)) : Prop :=
  ∀ e ∈ m, ∀ x ∈ e, 1 ≤ x ∧ x ≤ 100000

def WinnerNeLoser (m : List (List Int)) : Prop :=
  ∀ e ∈ m, ∀ w l, e[0]? = some w → e[1]? = some l → w ≠ l

def MatchesPairwiseDistinct (m : List (List Int)) : Prop :=
  ∀ i1 i2, i1 < i2 → i2 < m.length →
    ¬ (winnerAt m i1 = winnerAt m i2 ∧ loserAt m i1 = loserAt m i2)

def IsRenaming (m₁ m₂ : List (List Int)) (f : Nat → Nat) : Prop :=
  (∀ i, i < m₁.length → f i < m₂.length) ∧
  (∀ i, i < m₁.length →
    winnerAt m₂ (f i) = winnerAt m₁ i ∧ loserAt m₂ (f i) = loserAt m₁ i) ∧
  (∀ i j, i < m₁.length → j < m₁.length → f i = f j → i = j) ∧
  (∀ j, j < m₂.length → ∃ i, i < m₁.length ∧ f i = j)

/-- The function returns a result r and does not fail. It satisfies len(r) = 2. For every i64 value p, p occurs in r[0] if and only if p occurs in some match entry and p has no loss, i.e. (exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p)) and (there is no j with 0 <= j < len(matches) and matches[j][1] = p). For every i64 value p, p occurs in r[1] if and only if p occurs in some match entry and p has exactly one loss, i.e. (exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p)) and (there is exactly one j with 0 <= j < len(matches) and matches[j][1] = p). Finally, for each b in {0,1}, r[b] is strictly increasing: for all indices j,k with 0 <= j < k < len(r[b]), r[b][j] < r[b][k]. Here 'p occurs in r[b]' means there exists t with 0 <= t < len(r[b]) and r[b][t] = p.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_1 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r ∧
      r.val.length = 2 ∧
      (∀ p : Int, OccursIn p (answerRow r 0) ↔
        OccursInMatches p (matchMatrix «matches») ∧ NoLoss p (matchMatrix «matches»)) ∧
      (∀ p : Int, OccursIn p (answerRow r 1) ↔
        OccursInMatches p (matchMatrix «matches») ∧ OneLoss p (matchMatrix «matches»)) ∧
      StrictlyIncreasing (answerRow r 0) ∧
      StrictlyIncreasing (answerRow r 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r ∧
      r.val.length = 2 ∧
      (∀ p : Int, OccursIn p (answerRow r 0) ↔
        OccursInMatches p (matchMatrix «matches») ∧ NoLoss p (matchMatrix «matches»)) ∧
      (∀ p : Int, OccursIn p (answerRow r 1) ↔
        OccursInMatches p (matchMatrix «matches») ∧ OneLoss p (matchMatrix «matches»)) ∧
      StrictlyIncreasing (answerRow r 0) ∧
      StrictlyIncreasing (answerRow r 1)) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_2 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 2.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_3 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every i64 value p, if p occurs in some match entry and has no loss (exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p), and no j with 0 <= j < len(matches) and matches[j][1] = p), then p occurs in r[0] (there exists t with 0 <= t < len(r[0]) and r[0][t] = p).
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_4 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, OccursInMatches p (matchMatrix «matches») →
        NoLoss p (matchMatrix «matches») → OccursIn p (answerRow r 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, OccursInMatches p (matchMatrix «matches») →
        NoLoss p (matchMatrix «matches») → OccursIn p (answerRow r 0)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every index t with 0 <= t < len(r[0]), letting p = r[0][t], p occurs in some match entry and has no loss: there exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p), and there is no j with 0 <= j < len(matches) and matches[j][1] = p.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_5 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ (t : Nat) (ht : t < (answerRow r 0).length) (p : Int),
        (answerRow r 0)[t] = p →
        OccursInMatches p (matchMatrix «matches») ∧ NoLoss p (matchMatrix «matches») := by
  sorry

theorem spec_5_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ (t : Nat) (ht : t < (answerRow r 0).length) (p : Int),
        (answerRow r 0)[t] = p →
        OccursInMatches p (matchMatrix «matches») ∧ NoLoss p (matchMatrix «matches»)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every i64 value p, if p occurs in some match entry and has exactly one loss (exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p), and there is exactly one j with 0 <= j < len(matches) and matches[j][1] = p), then p occurs in r[1] (there exists t with 0 <= t < len(r[1]) and r[1][t] = p).
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_6 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, OccursInMatches p (matchMatrix «matches») →
        OneLoss p (matchMatrix «matches») → OccursIn p (answerRow r 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, OccursInMatches p (matchMatrix «matches») →
        OneLoss p (matchMatrix «matches») → OccursIn p (answerRow r 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every index t with 0 <= t < len(r[1]), letting p = r[1][t], p occurs in some match entry and has exactly one loss: there exists i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p), and there is exactly one j with 0 <= j < len(matches) and matches[j][1] = p.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_7 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ (t : Nat) (ht : t < (answerRow r 1).length) (p : Int),
        (answerRow r 1)[t] = p →
        OccursInMatches p (matchMatrix «matches») ∧ OneLoss p (matchMatrix «matches») := by
  sorry

theorem spec_7_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ (t : Nat) (ht : t < (answerRow r 1).length) (p : Int),
        (answerRow r 1)[t] = p →
        OccursInMatches p (matchMatrix «matches») ∧ OneLoss p (matchMatrix «matches»)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, the list r[0] is strictly increasing: for all indices j,k with 0 <= j < k < len(r[0]), r[0][j] < r[0][k].
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_8 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      StrictlyIncreasing (answerRow r 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      StrictlyIncreasing (answerRow r 0)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, the list r[1] is strictly increasing: for all indices j,k with 0 <= j < k < len(r[1]), r[1][j] < r[1][k].
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_9 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      StrictlyIncreasing (answerRow r 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      StrictlyIncreasing (answerRow r 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, no i64 value occurs in both r[0] and r[1]: there do not exist indices t0,t1 and a value p with 0 <= t0 < len(r[0]), 0 <= t1 < len(r[1]), r[0][t0] = p, and r[1][t1] = p.
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_10 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ¬ ∃ p : Int, OccursIn p (answerRow r 0) ∧ OccursIn p (answerRow r 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ¬ ∃ p : Int, OccursIn p (answerRow r 0) ∧ OccursIn p (answerRow r 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every i64 value p, if p has at least two losses (there exist distinct indices j1,j2 with 0 <= j1 < len(matches), 0 <= j2 < len(matches), j1 != j2, matches[j1][1] = p, and matches[j2][1] = p), then p does not occur in r[0] and does not occur in r[1].
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_11 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, AtLeastTwoLosses p (matchMatrix «matches») →
        ¬ OccursIn p (answerRow r 0) ∧ ¬ OccursIn p (answerRow r 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, AtLeastTwoLosses p (matchMatrix «matches») →
        ¬ OccursIn p (answerRow r 0) ∧ ¬ OccursIn p (answerRow r 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, for every i64 value p, if p does not occur in any match entry (there is no i with 0 <= i < len(matches) and (matches[i][0] = p or matches[i][1] = p)), then p occurs in neither r[0] nor r[1].
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_12 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, ¬ OccursInMatches p (matchMatrix «matches») →
        ¬ OccursIn p (answerRow r 0) ∧ ¬ OccursIn p (answerRow r 1) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      ∀ p : Int, ¬ OccursInMatches p (matchMatrix «matches») →
        ¬ OccursIn p (answerRow r 0) ∧ ¬ OccursIn p (answerRow r 1)) := by
  sorry

/-- Whenever the function returns a result r with len(r) = 2, the two answer lists are not larger than the number of matches: len(r[0]) <= len(matches) and len(r[1]) <= len(matches).
  Preconditions: 1 <= len(matches) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]). -/
theorem spec_13 («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      (answerRow r 0).length ≤ (matchMatrix «matches»).length ∧
      (answerRow r 1).length ≤ (matchMatrix «matches»).length := by
  sorry

theorem spec_13_neg :
    ¬ (∀ («matches» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»)), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r → r.val.length = 2 →
      (answerRow r 0).length ≤ (matchMatrix «matches»).length ∧
      (answerRow r 1).length ≤ (matchMatrix «matches»).length) := by
  sorry

/-- Whenever the function returns a result r for matches and a result r2 for matches2, the results are equal: r = r2.
  Preconditions: 1 <= len(matches) <= 100000; 1 <= len(matches2) <= 100000; for every i with 0 <= i < len(matches), len(matches[i]) = 2; for every i with 0 <= i < len(matches2), len(matches2[i]) = 2; for every i with 0 <= i < len(matches) and every j in {0,1}, 1 <= matches[i][j] <= 100000; for every i with 0 <= i < len(matches2) and every j in {0,1}, 1 <= matches2[i][j] <= 100000; for every i with 0 <= i < len(matches), matches[i][0] != matches[i][1]; for every i with 0 <= i < len(matches2), matches2[i][0] != matches2[i][1]; for every i1,i2 with 0 <= i1 < i2 < len(matches), not (matches[i1][0] = matches[i2][0] and matches[i1][1] = matches[i2][1]); for every i1,i2 with 0 <= i1 < i2 < len(matches2), not (matches2[i1][0] = matches2[i2][0] and matches2[i1][1] = matches2[i2][1]); there is a bijection f from {i | 0 <= i < len(matches)} to {i | 0 <= i < len(matches2)} such that for every i with 0 <= i < len(matches), matches2[f(i)][0] = matches[i][0] and matches2[f(i)][1] = matches[i][1]. -/
theorem spec_14 («matches» «matches2» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_len2 : LenBounds (matchMatrix «matches2»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_rows2 : RowsLen2 (matchMatrix «matches2»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_range2 : EntriesInRange (matchMatrix «matches2»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_ne2 : WinnerNeLoser (matchMatrix «matches2»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»))
    (h_distinct2 : MatchesPairwiseDistinct (matchMatrix «matches2»))
    (h_perm : ∃ f : Nat → Nat,
      IsRenaming (matchMatrix «matches») (matchMatrix «matches2») f) :
    ∀ r r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r →
      Aegis.FindWinners.find_winners «matches2» = ok r2 → r = r2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ («matches» «matches2» : Slice (alloc.vec.Vec Std.I64))
    (h_len : LenBounds (matchMatrix «matches»))
    (h_len2 : LenBounds (matchMatrix «matches2»))
    (h_rows : RowsLen2 (matchMatrix «matches»))
    (h_rows2 : RowsLen2 (matchMatrix «matches2»))
    (h_range : EntriesInRange (matchMatrix «matches»))
    (h_range2 : EntriesInRange (matchMatrix «matches2»))
    (h_ne : WinnerNeLoser (matchMatrix «matches»))
    (h_ne2 : WinnerNeLoser (matchMatrix «matches2»))
    (h_distinct : MatchesPairwiseDistinct (matchMatrix «matches»))
    (h_distinct2 : MatchesPairwiseDistinct (matchMatrix «matches2»))
    (h_perm : ∃ f : Nat → Nat,
      IsRenaming (matchMatrix «matches») (matchMatrix «matches2») f), ∀ r r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.FindWinners.find_winners «matches» = ok r →
      Aegis.FindWinners.find_winners «matches2» = ok r2 → r = r2) := by
  sorry

end AegisSpec.FindWinners
