import Aegis.RestoreMatrix.Code.Funs

/-!
# Specifications of `Aegis.RestoreMatrix.restore_matrix`

LeetCode problem `find-valid-matrix-given-row-and-column-sums`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RestoreMatrix

  set_option autoImplicit false

  abbrev Matrix : Type := alloc.vec.Vec (alloc.vec.Vec I64)

  def ival (x : I64) : Int := x.val

  def ivals (l : List I64) : List Int := l.map ival

  def vals (s : Slice I64) : List Int := ivals s.val

  def rows (r : Matrix) : List (List Int) := (r.val).map (fun row => ivals row.val)

  def sumRange (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).sum

  def intAt (l : List Int) (i : Nat) : Int := l.getD i 0

  def rowAt (m : List (List Int)) (i : Nat) : List Int := m.getD i []

  def entry (m : List (List Int)) (i j : Nat) : Int := intAt (rowAt m i) j

  def rowTotal (m : List (List Int)) (i cols : Nat) : Int := sumRange cols (fun j => entry m i j)

  def colTotal (m : List (List Int)) (j nrows : Nat) : Int := sumRange nrows (fun i => entry m i j)

  /-- Whenever the function returns a result r, r is a 2D array (vector of vectors) of size len(rowSum) × len(colSum) such that: (1) for every i with 0 <= i < len(rowSum) and every j with 0 <= j < len(colSum), r[i][j] >= 0; (2) for every i with 0 <= i < len(rowSum), the sum of the elements of r[i] equals rowSum[i], i.e., Σ_{j=0}^{len(colSum)-1} r[i][j] = rowSum[i]; (3) for every j with 0 <= j < len(colSum), the sum of the j-th elements of all rows of r equals colSum[j], i.e., Σ_{i=0}^{len(rowSum)-1} r[i][j] = colSum[j].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_1 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      (rows r).length = (vals rowSum).length ∧
        (∀ i, i < (vals rowSum).length → (rowAt (rows r) i).length = (vals colSum).length) ∧
        (∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
          0 ≤ entry (rows r) i j) ∧
        (∀ i, i < (vals rowSum).length →
          rowTotal (rows r) i (vals colSum).length = intAt (vals rowSum) i) ∧
        (∀ j, j < (vals colSum).length →
          colTotal (rows r) j (vals rowSum).length = intAt (vals colSum) j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), (rows r).length = (vals rowSum).length ∧
          (∀ i, i < (vals rowSum).length → (rowAt (rows r) i).length = (vals colSum).length) ∧
          (∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
            0 ≤ entry (rows r) i j) ∧
          (∀ i, i < (vals rowSum).length →
            rowTotal (rows r) i (vals colSum).length = intAt (vals rowSum) i) ∧
          (∀ j, j < (vals colSum).length →
            colTotal (rows r) j (vals rowSum).length = intAt (vals colSum) j)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (i.e., it does not fail, panic, or overflow).
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_2 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum) :
      ∃ r : Matrix, Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum), ∃ r : Matrix, Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(rowSum) and for every i with 0 <= i < len(rowSum), len(r[i]) = len(colSum).
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_3 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      (rows r).length = (vals rowSum).length ∧
        ∀ i, i < (vals rowSum).length → (rowAt (rows r) i).length = (vals colSum).length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), (rows r).length = (vals rowSum).length ∧
          ∀ i, i < (vals rowSum).length → (rowAt (rows r) i).length = (vals colSum).length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(rowSum) and every j with 0 <= j < len(colSum), r[i][j] >= 0.
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_4 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
        0 ≤ entry (rows r) i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
          0 ≤ entry (rows r) i j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(rowSum), the sum of the elements of the i-th row of r equals rowSum[i], i.e., Σ_{j=0}^{len(colSum)-1} r[i][j] = rowSum[i].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_5 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      ∀ i, i < (vals rowSum).length →
        rowTotal (rows r) i (vals colSum).length = intAt (vals rowSum) i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), ∀ i, i < (vals rowSum).length →
          rowTotal (rows r) i (vals colSum).length = intAt (vals rowSum) i) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(colSum), the sum of the j-th elements of all rows of r equals colSum[j], i.e., Σ_{i=0}^{len(rowSum)-1} r[i][j] = colSum[j].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_6 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      ∀ j, j < (vals colSum).length →
        colTotal (rows r) j (vals rowSum).length = intAt (vals colSum) j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), ∀ j, j < (vals colSum).length →
          colTotal (rows r) j (vals rowSum).length = intAt (vals colSum) j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(rowSum) and every j with 0 <= j < len(colSum), r[i][j] <= rowSum[i] and r[i][j] <= colSum[j].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_7 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
        entry (rows r) i j ≤ intAt (vals rowSum) i ∧
          entry (rows r) i j ≤ intAt (vals colSum) j := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
          entry (rows r) i j ≤ intAt (vals rowSum) i ∧
            entry (rows r) i j ≤ intAt (vals colSum) j) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(rowSum), if rowSum[i] = 0 then for every j with 0 <= j < len(colSum), r[i][j] = 0; and for every j with 0 <= j < len(colSum), if colSum[j] = 0 then for every i with 0 <= i < len(rowSum), r[i][j] = 0.
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_8 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      (∀ i, i < (vals rowSum).length → intAt (vals rowSum) i = 0 →
        ∀ j, j < (vals colSum).length → entry (rows r) i j = 0) ∧
      (∀ j, j < (vals colSum).length → intAt (vals colSum) j = 0 →
        ∀ i, i < (vals rowSum).length → entry (rows r) i j = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), (∀ i, i < (vals rowSum).length → intAt (vals rowSum) i = 0 →
          ∀ j, j < (vals colSum).length → entry (rows r) i j = 0) ∧
        (∀ j, j < (vals colSum).length → intAt (vals colSum) j = 0 →
          ∀ i, i < (vals rowSum).length → entry (rows r) i j = 0)) := by
    sorry

  /-- Whenever the function returns a result r, the sum of all elements of r equals sum(rowSum), i.e., Σ_{i=0}^{len(rowSum)-1} Σ_{j=0}^{len(colSum)-1} r[i][j] = Σ_{i=0}^{len(rowSum)-1} rowSum[i]. By the precondition, this also equals sum(colSum).
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_9 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r) :
      sumRange (vals rowSum).length
          (fun i => rowTotal (rows r) i (vals colSum).length) =
        sumRange (vals rowSum).length (fun i => intAt (vals rowSum) i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r), sumRange (vals rowSum).length
            (fun i => rowTotal (rows r) i (vals colSum).length) =
          sumRange (vals rowSum).length (fun i => intAt (vals rowSum) i)) := by
    sorry

  /-- Whenever the function returns a result r and len(rowSum) = 1, then len(r) = 1 and for every j with 0 <= j < len(colSum), r[0][j] = colSum[j].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_10 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
      (h_one : (vals rowSum).length = 1) :
      (rows r).length = 1 ∧
        ∀ j, j < (vals colSum).length → entry (rows r) 0 j = intAt (vals colSum) j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
        (h_one : (vals rowSum).length = 1), (rows r).length = 1 ∧
          ∀ j, j < (vals colSum).length → entry (rows r) 0 j = intAt (vals colSum) j) := by
    sorry

  /-- Whenever the function returns a result r and len(colSum) = 1, then for every i with 0 <= i < len(rowSum), len(r[i]) = 1 and r[i][0] = rowSum[i].
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_11 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
      (h_one : (vals colSum).length = 1) :
      ∀ i, i < (vals rowSum).length →
        (rowAt (rows r) i).length = 1 ∧ entry (rows r) i 0 = intAt (vals rowSum) i := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
        (h_one : (vals colSum).length = 1), ∀ i, i < (vals rowSum).length →
          (rowAt (rows r) i).length = 1 ∧ entry (rows r) i 0 = intAt (vals rowSum) i) := by
    sorry

  /-- Whenever the function returns a result r and for every i with 0 <= i < len(rowSum), rowSum[i] = 0, then for every i with 0 <= i < len(rowSum) and every j with 0 <= j < len(colSum), r[i][j] = 0.
    Preconditions: len(rowSum) >= 1, len(colSum) >= 1, len(rowSum) <= 500, len(colSum) <= 500. For every i with 0 <= i < len(rowSum), 0 <= rowSum[i] <= 10^8. For every j with 0 <= j < len(colSum), 0 <= colSum[j] <= 10^8. sum(rowSum) = sum(colSum), where sum(rowSum) = Σ_{i=0}^{len(rowSum)-1} rowSum[i] and sum(colSum) = Σ_{j=0}^{len(colSum)-1} colSum[j]. -/
  theorem spec_12 (rowSum colSum : Slice I64)
      (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
      (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
      (hrow : ∀ i, i < (vals rowSum).length →
        0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
      (hcol : ∀ j, j < (vals colSum).length →
        0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
      (hsum : (vals rowSum).sum = (vals colSum).sum)
      (r : Matrix)
      (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
      (hzero : ∀ i, i < (vals rowSum).length → intAt (vals rowSum) i = 0) :
      ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
        entry (rows r) i j = 0 := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (rowSum colSum : Slice I64)
        (hn : 1 ≤ (vals rowSum).length) (hm : 1 ≤ (vals colSum).length)
        (hn_le : (vals rowSum).length ≤ 500) (hm_le : (vals colSum).length ≤ 500)
        (hrow : ∀ i, i < (vals rowSum).length →
          0 ≤ intAt (vals rowSum) i ∧ intAt (vals rowSum) i ≤ 10 ^ 8)
        (hcol : ∀ j, j < (vals colSum).length →
          0 ≤ intAt (vals colSum) j ∧ intAt (vals colSum) j ≤ 10 ^ 8)
        (hsum : (vals rowSum).sum = (vals colSum).sum)
        (r : Matrix)
        (hr : Aegis.RestoreMatrix.restore_matrix rowSum colSum = ok r)
        (hzero : ∀ i, i < (vals rowSum).length → intAt (vals rowSum) i = 0), ∀ i j, i < (vals rowSum).length → j < (vals colSum).length →
          entry (rows r) i j = 0) := by
    sorry

  end AegisSpec.RestoreMatrix
