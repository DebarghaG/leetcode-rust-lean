import Aegis.ZigzagTraversal.Code.Funs

/-!
# Specifications of `Aegis.ZigzagTraversal.zigzag_traversal`

LeetCode problem `zigzag-grid-traversal-with-skip`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ZigzagTraversal

namespace AegisSpec.ZigzagTraversal

abbrev Grid := Slice (alloc.vec.Vec Std.I64)

abbrev OutVec := alloc.vec.Vec Std.I64

def numRows (grid : Grid) : Nat := grid.val.length

def rowWidth (grid : Grid) : Nat :=
  (grid.val.head?.map (fun row => row.val.length)).getD 0

def rowLen (grid : Grid) (i : Nat) : Nat := (grid.val[i]!).val.length

def cell (grid : Grid) (i j : Nat) : Int := (grid.val[i]!).val[j]!.val

def entry (r : OutVec) (k : Nat) : Int := r.val[k]!.val

def traversalIndex (k : Nat) : Nat := 2 * k

def stepRow (grid : Grid) (k : Nat) : Nat := traversalIndex k / rowWidth grid

def stepPos (grid : Grid) (k : Nat) : Nat := traversalIndex k % rowWidth grid

def zigCol (n : Nat) (i p : Nat) : Nat := if i % 2 = 0 then p else n - 1 - p

def stepCol (grid : Grid) (k : Nat) : Nat :=
  zigCol (rowWidth grid) (stepRow grid k) (stepPos grid k)

def stepCell (grid : Grid) (k : Nat) : Int := cell grid (stepRow grid k) (stepCol grid k)

/-- The function returns a result r. Let T = m*n. Then len(r) = (T + 1) div 2, and for every integer k with 0 <= k < len(r), setting t = 2*k, i = t div n, p = t mod n, and j = p if i is even and j = n - 1 - p if i is odd, we have r[k] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_1 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∃ r, zigzag_traversal grid = ok r ∧
      r.val.length = (numRows grid * rowWidth grid + 1) / 2 ∧
      (∀ k, k < r.val.length → entry r k = stepCell grid k) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∃ r, zigzag_traversal grid = ok r ∧
      r.val.length = (numRows grid * rowWidth grid + 1) / 2 ∧
      (∀ k, k < r.val.length → entry r k = stepCell grid k)) := by
  sorry

/-- The function does not fail: for every input satisfying the precondition, it returns some vector r rather than an error. In particular, no panic, out-of-bounds access, or integer overflow occurs.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_2 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∃ r, zigzag_traversal grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∃ r, zigzag_traversal grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = (len(grid) * len(grid[0]) + 1) div 2. Equivalently, len(r) = ceil(m*n/2), the number of even integers t with 0 <= t < m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_3 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      r.val.length = (numRows grid * rowWidth grid + 1) / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      r.val.length = (numRows grid * rowWidth grid + 1) / 2) := by
  sorry

/-- Whenever the function returns a result r, r[0] = grid[0][0].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_4 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r → entry r 0 = cell grid 0 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r → entry r 0 = cell grid 0 0) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k < len(r), 1 <= r[k] <= 2500.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_5 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k < r.val.length → 1 ≤ entry r k ∧ entry r k ≤ 2500 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k < r.val.length → 1 ≤ entry r k ∧ entry r k ≤ 2500) := by
  sorry

/-- Whenever the function returns a result r, define i_k = (2*k) div n for each k with 0 <= k < len(r). Then for every such k, 0 <= i_k < m; for every k with 0 <= k+1 < len(r), i_k <= i_{k+1} <= i_k + 1. Thus the source rows are nondecreasing and never skip a row between consecutive result entries.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_6 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      (∀ k, k < r.val.length → stepRow grid k < numRows grid) ∧
      (∀ k, k + 1 < r.val.length →
        stepRow grid k ≤ stepRow grid (k + 1) ∧ stepRow grid (k + 1) ≤ stepRow grid k + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      (∀ k, k < r.val.length → stepRow grid k < numRows grid) ∧
      (∀ k, k + 1 < r.val.length →
        stepRow grid k ≤ stepRow grid (k + 1) ∧ stepRow grid (k + 1) ≤ stepRow grid k + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k+1 < len(r), let t = 2*k, i = t div n, p = t mod n, t' = 2*(k+1), i' = t' div n, p' = t' mod n. If i' = i, then p' = p + 2. Consequently, if i is even the physical column increases by 2, and if i is odd the physical column decreases by 2.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_7 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k + 1 < r.val.length → stepRow grid (k + 1) = stepRow grid k →
        stepPos grid (k + 1) = stepPos grid k + 2 ∧
        (stepRow grid k % 2 = 0 → stepCol grid (k + 1) = stepCol grid k + 2) ∧
        (stepRow grid k % 2 = 1 → stepCol grid k = stepCol grid (k + 1) + 2) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k + 1 < r.val.length → stepRow grid (k + 1) = stepRow grid k →
        stepPos grid (k + 1) = stepPos grid k + 2 ∧
        (stepRow grid k % 2 = 0 → stepCol grid (k + 1) = stepCol grid k + 2) ∧
        (stepRow grid k % 2 = 1 → stepCol grid k = stepCol grid (k + 1) + 2)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 0 <= k+1 < len(r), let t = 2*k, i = t div n, p = t mod n, t' = 2*(k+1), i' = t' div n, p' = t' mod n. If i' != i, then i' = i + 1 and p' = p + 2 - n. In particular p' is either 0 or 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_8 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k + 1 < r.val.length → stepRow grid (k + 1) ≠ stepRow grid k →
        stepRow grid (k + 1) = stepRow grid k + 1 ∧
        stepPos grid (k + 1) = stepPos grid k + 2 - rowWidth grid ∧
        (stepPos grid (k + 1) = 0 ∨ stepPos grid (k + 1) = 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      ∀ k, k + 1 < r.val.length → stepRow grid (k + 1) ≠ stepRow grid k →
        stepRow grid (k + 1) = stepRow grid k + 1 ∧
        stepPos grid (k + 1) = stepPos grid k + 2 - rowWidth grid ∧
        (stepPos grid (k + 1) = 0 ∨ stepPos grid (k + 1) = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every row index i with 0 <= i < m and every traversal position p with 0 <= p < n within that row, the cell reached at position p of row i in the zigzag order is the source of exactly one entry of r if p is congruent to i*n modulo 2, and is the source of no entry of r otherwise. Equivalently, in row i the kept traversal positions are r_i, r_i+2, r_i+4, ... where r_i = 0 if i*n is even and r_i = 1 if i*n is odd.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_9 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      ∀ i p, i < numRows grid → p < rowWidth grid →
        ((∃! k, k < r.val.length ∧ stepRow grid k = i ∧ stepPos grid k = p) ↔
          p % 2 = (i * rowWidth grid) % 2) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      ∀ i p, i < numRows grid → p < rowWidth grid →
        ((∃! k, k < r.val.length ∧ stepRow grid k = i ∧ stepPos grid k = p) ↔
          p % 2 = (i * rowWidth grid) % 2)) := by
  sorry

/-- Whenever the function returns a result r, let t_last = 2*(len(r)-1). Then t_last div n = m - 1. Equivalently, the last entry r[len(r)-1] comes from the last row of grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 50, every row of grid has length n, 2 <= n <= 50, and for every 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 2500. -/
theorem spec_10 (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500) :
    ∀ r, zigzag_traversal grid = ok r →
      0 < r.val.length ∧
      (2 * (r.val.length - 1)) / rowWidth grid = numRows grid - 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid)
    (hm_lo : 2 ≤ numRows grid) (hm_hi : numRows grid ≤ 50)
    (hrow : ∀ i, i < numRows grid → rowLen grid i = rowWidth grid)
    (hn_lo : 2 ≤ rowWidth grid) (hn_hi : rowWidth grid ≤ 50)
    (hbound : ∀ i j, i < numRows grid → j < rowWidth grid →
      1 ≤ cell grid i j ∧ cell grid i j ≤ 2500), ∀ r, zigzag_traversal grid = ok r →
      0 < r.val.length ∧
      (2 * (r.val.length - 1)) / rowWidth grid = numRows grid - 1) := by
  sorry

end AegisSpec.ZigzagTraversal
