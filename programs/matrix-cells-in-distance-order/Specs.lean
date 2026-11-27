import Aegis.AllCellsDistOrder.Code.Funs

/-!
# Specifications of `Aegis.AllCellsDistOrder.all_cells_dist_order`

LeetCode problem `matrix-cells-in-distance-order`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace AegisSpec.AllCellsDistOrder

abbrev IntVec := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

abbrev OutVec := Aeneas.Std.alloc.vec.Vec IntVec

def cellAt (ans : List IntVec) (k : ℕ) : List I64 :=
  match ans[k]? with
  | some cell => cell.val
  | none => []

def cellRow (cell : List I64) : ℤ :=
  match cell[0]? with
  | some r => r.val
  | none => 0

def cellCol (cell : List I64) : ℤ :=
  match cell[1]? with
  | some c => c.val
  | none => 0

def rowOf (ans : List IntVec) (k : ℕ) : ℤ :=
  cellRow (cellAt ans k)

def colOf (ans : List IntVec) (k : ℕ) : ℤ :=
  cellCol (cellAt ans k)

def distToCenter (r c rCenter cCenter : ℤ) : ℤ :=
  |r - rCenter| + |c - cCenter|

def distOf (ans : List IntVec) (k : ℕ) (rCenter cCenter : ℤ) : ℤ :=
  distToCenter (rowOf ans k) (colOf ans k) rCenter cCenter

def maxCenterDist (rows cols rCenter cCenter : ℤ) : ℤ :=
  max rCenter (rows - 1 - rCenter) + max cCenter (cols - 1 - cCenter)

def gridDistCount (rows cols rCenter cCenter t : ℤ) : ℕ :=
  ((List.range rows.toNat).product (List.range cols.toNat)).countP (fun p =>
    decide (distToCenter (p.1 : ℤ) (p.2 : ℤ) rCenter cCenter = t))

def outDistCount (ans : List IntVec) (rCenter cCenter t : ℤ) : ℕ :=
  (List.range ans.length).countP (fun k =>
    decide ((cellAt ans k).length = 2 ∧ distOf ans k rCenter cCenter = t))

def outRowCount (ans : List IntVec) (r : ℤ) : ℕ :=
  (List.range ans.length).countP (fun k =>
    decide ((cellAt ans k).length = 2 ∧ rowOf ans k = r))

def outColCount (ans : List IntVec) (c : ℤ) : ℕ :=
  (List.range ans.length).countP (fun k =>
    decide ((cellAt ans k).length = 2 ∧ colOf ans k = c))

def outCenterCount (ans : List IntVec) (rCenter cCenter : ℤ) : ℕ :=
  (List.range ans.length).countP (fun k =>
    decide ((cellAt ans k).length = 2 ∧ rowOf ans k = rCenter ∧ colOf ans k = cCenter))

/-- The function returns a result ans (it does not fail) such that: (1) len(ans) = rows * cols; (2) for every k with 0 <= k < len(ans), len(ans[k]) = 2, 0 <= ans[k][0] < rows, and 0 <= ans[k][1] < cols; (3) the coordinate pairs (ans[k][0], ans[k][1]) for 0 <= k < len(ans) are pairwise distinct; (4) for every cell (r, c) with 0 <= r < rows and 0 <= c < cols, there exists k with 0 <= k < len(ans), ans[k][0] = r, and ans[k][1] = c; and (5) for every i, j with 0 <= i < j < len(ans), |ans[i][0] - rCenter| + |ans[i][1] - cCenter| <= |ans[j][0] - rCenter| + |ans[j][1] - cCenter|.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_1 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val) :
    ∃ ans : OutVec,
      Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans ∧
      ans.val.length = (rows.val * cols.val).toNat ∧
      (∀ k : ℕ, k < ans.val.length →
        (cellAt ans.val k).length = 2 ∧
          0 ≤ rowOf ans.val k ∧ rowOf ans.val k < rows.val ∧
            0 ≤ colOf ans.val k ∧ colOf ans.val k < cols.val) ∧
      (∀ i j : ℕ, i < j → j < ans.val.length →
        ¬(rowOf ans.val i = rowOf ans.val j ∧ colOf ans.val i = colOf ans.val j)) ∧
      (∀ r c : ℤ, 0 ≤ r → r < rows.val → 0 ≤ c → c < cols.val →
        ∃ k : ℕ, k < ans.val.length ∧ rowOf ans.val k = r ∧ colOf ans.val k = c) ∧
      (∀ i j : ℕ, i < j → j < ans.val.length →
        distOf ans.val i rCenter.val cCenter.val ≤
          distOf ans.val j rCenter.val cCenter.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val), ∃ ans : OutVec,
      Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans ∧
      ans.val.length = (rows.val * cols.val).toNat ∧
      (∀ k : ℕ, k < ans.val.length →
        (cellAt ans.val k).length = 2 ∧
          0 ≤ rowOf ans.val k ∧ rowOf ans.val k < rows.val ∧
            0 ≤ colOf ans.val k ∧ colOf ans.val k < cols.val) ∧
      (∀ i j : ℕ, i < j → j < ans.val.length →
        ¬(rowOf ans.val i = rowOf ans.val j ∧ colOf ans.val i = colOf ans.val j)) ∧
      (∀ r c : ℤ, 0 ≤ r → r < rows.val → 0 ≤ c → c < cols.val →
        ∃ k : ℕ, k < ans.val.length ∧ rowOf ans.val k = r ∧ colOf ans.val k = c) ∧
      (∀ i j : ℕ, i < j → j < ans.val.length →
        distOf ans.val i rCenter.val cCenter.val ≤
          distOf ans.val j rCenter.val cCenter.val)) := by
  sorry

/-- The function returns a result ans; it does not fail.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_2 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val) :
    ∃ ans : OutVec,
      Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val), ∃ ans : OutVec,
      Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) := by
  sorry

/-- Whenever the function returns a result ans, the number of entries of ans is rows * cols; that is, len(ans) = rows * cols.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_3 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ans.val.length = (rows.val * cols.val).toNat := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ans.val.length = (rows.val * cols.val).toNat) := by
  sorry

/-- Whenever the function returns a result ans, for every k with 0 <= k < len(ans), the inner vector ans[k] has length 2; that is, len(ans[k]) = 2.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_4 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2) := by
  sorry

/-- Whenever the function returns a result ans, for every k with 0 <= k < len(ans) such that len(ans[k]) = 2, the coordinates satisfy 0 <= ans[k][0] < rows and 0 <= ans[k][1] < cols.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_5 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2 →
      0 ≤ rowOf ans.val k ∧ rowOf ans.val k < rows.val ∧
        0 ≤ colOf ans.val k ∧ colOf ans.val k < cols.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2 →
      0 ≤ rowOf ans.val k ∧ rowOf ans.val k < rows.val ∧
        0 ≤ colOf ans.val k ∧ colOf ans.val k < cols.val) := by
  sorry

/-- Whenever the function returns a result ans, for every i, j with 0 <= i < j < len(ans), if len(ans[i]) = 2 and len(ans[j]) = 2, then it is not the case that ans[i][0] = ans[j][0] and ans[i][1] = ans[j][1].
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_6 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ i j : ℕ, i < j → j < ans.val.length →
      (cellAt ans.val i).length = 2 → (cellAt ans.val j).length = 2 →
        ¬(rowOf ans.val i = rowOf ans.val j ∧ colOf ans.val i = colOf ans.val j) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ i j : ℕ, i < j → j < ans.val.length →
      (cellAt ans.val i).length = 2 → (cellAt ans.val j).length = 2 →
        ¬(rowOf ans.val i = rowOf ans.val j ∧ colOf ans.val i = colOf ans.val j)) := by
  sorry

/-- Whenever the function returns a result ans, for every r and c with 0 <= r < rows and 0 <= c < cols, there exists an index k with 0 <= k < len(ans), len(ans[k]) = 2, ans[k][0] = r, and ans[k][1] = c.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_7 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ r c : ℤ, 0 ≤ r → r < rows.val → 0 ≤ c → c < cols.val →
      ∃ k : ℕ, k < ans.val.length ∧ (cellAt ans.val k).length = 2 ∧
        rowOf ans.val k = r ∧ colOf ans.val k = c := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ r c : ℤ, 0 ≤ r → r < rows.val → 0 ≤ c → c < cols.val →
      ∃ k : ℕ, k < ans.val.length ∧ (cellAt ans.val k).length = 2 ∧
        rowOf ans.val k = r ∧ colOf ans.val k = c) := by
  sorry

/-- Whenever the function returns a result ans, for every i, j with 0 <= i < j < len(ans) such that len(ans[i]) = 2 and len(ans[j]) = 2, |ans[i][0] - rCenter| + |ans[i][1] - cCenter| <= |ans[j][0] - rCenter| + |ans[j][1] - cCenter|.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_8 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ i j : ℕ, i < j → j < ans.val.length →
      (cellAt ans.val i).length = 2 → (cellAt ans.val j).length = 2 →
        distOf ans.val i rCenter.val cCenter.val ≤
          distOf ans.val j rCenter.val cCenter.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ i j : ℕ, i < j → j < ans.val.length →
      (cellAt ans.val i).length = 2 → (cellAt ans.val j).length = 2 →
        distOf ans.val i rCenter.val cCenter.val ≤
          distOf ans.val j rCenter.val cCenter.val) := by
  sorry

/-- Whenever the function returns a result ans, for every integer t >= 0, the number of indices k with 0 <= k < len(ans), len(ans[k]) = 2, and |ans[k][0] - rCenter| + |ans[k][1] - cCenter| = t equals the number of pairs (r, c) with 0 <= r < rows, 0 <= c < cols, and |r - rCenter| + |c - cCenter| = t.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_9 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ t : ℤ, 0 ≤ t →
      outDistCount ans.val rCenter.val cCenter.val t =
        gridDistCount rows.val cols.val rCenter.val cCenter.val t := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ t : ℤ, 0 ≤ t →
      outDistCount ans.val rCenter.val cCenter.val t =
        gridDistCount rows.val cols.val rCenter.val cCenter.val t) := by
  sorry

/-- Whenever the function returns a result ans, len(ans) > 0, len(ans[0]) = 2, ans[0][0] = rCenter, and ans[0][1] = cCenter.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_10 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ans.val.length > 0 ∧ (cellAt ans.val 0).length = 2 ∧
      rowOf ans.val 0 = rCenter.val ∧ colOf ans.val 0 = cCenter.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ans.val.length > 0 ∧ (cellAt ans.val 0).length = 2 ∧
      rowOf ans.val 0 = rCenter.val ∧ colOf ans.val 0 = cCenter.val) := by
  sorry

/-- Whenever the function returns a result ans, there is exactly one index k with 0 <= k < len(ans), len(ans[k]) = 2, ans[k][0] = rCenter, and ans[k][1] = cCenter.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_11 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    outCenterCount ans.val rCenter.val cCenter.val = 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), outCenterCount ans.val rCenter.val cCenter.val = 1) := by
  sorry

/-- Whenever the function returns a result ans, let M = max(rCenter, rows - 1 - rCenter) + max(cCenter, cols - 1 - cCenter). Then every k with 0 <= k < len(ans) and len(ans[k]) = 2 satisfies |ans[k][0] - rCenter| + |ans[k][1] - cCenter| <= M, and there exists some k with 0 <= k < len(ans), len(ans[k]) = 2, and |ans[k][0] - rCenter| + |ans[k][1] - cCenter| = M.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_12 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    (∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2 →
      distOf ans.val k rCenter.val cCenter.val ≤
        maxCenterDist rows.val cols.val rCenter.val cCenter.val) ∧
      (∃ k : ℕ, k < ans.val.length ∧ (cellAt ans.val k).length = 2 ∧
        distOf ans.val k rCenter.val cCenter.val =
          maxCenterDist rows.val cols.val rCenter.val cCenter.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), (∀ k : ℕ, k < ans.val.length → (cellAt ans.val k).length = 2 →
      distOf ans.val k rCenter.val cCenter.val ≤
        maxCenterDist rows.val cols.val rCenter.val cCenter.val) ∧
      (∃ k : ℕ, k < ans.val.length ∧ (cellAt ans.val k).length = 2 ∧
        distOf ans.val k rCenter.val cCenter.val =
          maxCenterDist rows.val cols.val rCenter.val cCenter.val)) := by
  sorry

/-- Whenever the function returns a result ans, for every row r with 0 <= r < rows, the number of indices k with 0 <= k < len(ans), len(ans[k]) = 2, and ans[k][0] = r is exactly cols.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_13 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ r : ℤ, 0 ≤ r → r < rows.val → outRowCount ans.val r = cols.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ r : ℤ, 0 ≤ r → r < rows.val → outRowCount ans.val r = cols.val.toNat) := by
  sorry

/-- Whenever the function returns a result ans, for every column c with 0 <= c < cols, the number of indices k with 0 <= k < len(ans), len(ans[k]) = 2, and ans[k][1] = c is exactly rows.
  Preconditions: rows, cols, rCenter, and cCenter are 64-bit signed integers satisfying 1 <= rows <= 100, 1 <= cols <= 100, 0 <= rCenter < rows, and 0 <= cCenter < cols. -/
theorem spec_14 (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans) :
    ∀ c : ℤ, 0 ≤ c → c < cols.val → outColCount ans.val c = rows.val.toNat := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (rows cols rCenter cCenter : I64)
    (hrows_lo : 1 ≤ rows.val) (hrows_hi : rows.val ≤ 100)
    (hcols_lo : 1 ≤ cols.val) (hcols_hi : cols.val ≤ 100)
    (hrc_lo : 0 ≤ rCenter.val) (hrc_hi : rCenter.val < rows.val)
    (hcc_lo : 0 ≤ cCenter.val) (hcc_hi : cCenter.val < cols.val)
    (ans : OutVec)
    (hans : Aegis.AllCellsDistOrder.all_cells_dist_order rows cols rCenter cCenter = ok ans), ∀ c : ℤ, 0 ≤ c → c < cols.val → outColCount ans.val c = rows.val.toNat) := by
  sorry

end AegisSpec.AllCellsDistOrder
