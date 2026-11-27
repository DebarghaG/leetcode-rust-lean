import Aegis.LargestLocal.Code.Funs

/-!
# Specifications of `Aegis.LargestLocal.largest_local`

LeetCode problem `largest-local-values-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LargestLocal

def matrix (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val)

def outMatrix (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
  r.val.map (fun row => row.val)

def rowOf (M : List (List Int)) (i : Nat) : List Int :=
  M.getD i []

def cellOf (M : List (List Int)) (i j : Nat) : Int :=
  (rowOf M i).getD j 0

def window (M : List (List Int)) (i j : Nat) : List Int :=
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b => cellOf M (i + a) (j + b)))

def winMax (M : List (List Int)) (i j : Nat) : Int :=
  match window M i j with
  | [] => 0
  | x :: xs => xs.foldl max x

/-- Whenever largest_local(grid) returns a result r, we have len(r) = n - 2, len(r[i]) = n - 2 for every i with 0 <= i < n - 2, and for every i,j with 0 <= i,j < n - 2, r[i][j] = max{ grid[p][q] | i <= p <= i + 2 and j <= q <= j + 2 }.
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r) :
    (outMatrix r).length = n - 2 ∧
      (∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2) ∧
      (∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
        cellOf (outMatrix r) i j = winMax (matrix grid) i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r), (outMatrix r).length = n - 2 ∧
      (∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2) ∧
      (∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
        cellOf (outMatrix r) i j = winMax (matrix grid) i j)) := by
  sorry

/-- Whenever largest_local(grid) returns a result r, len(r) = n - 2.
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r) :
    (outMatrix r).length = n - 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r), (outMatrix r).length = n - 2) := by
  sorry

/-- Whenever largest_local(grid) returns a result r, for every i with 0 <= i < len(r), len(r[i]) = n - 2.
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r) :
    ∀ (i : Nat), i < (outMatrix r).length → (rowOf (outMatrix r) i).length = n - 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r), ∀ (i : Nat), i < (outMatrix r).length → (rowOf (outMatrix r) i).length = n - 2) := by
  sorry

/-- Whenever largest_local(grid) returns a result r and r has len(r) = n - 2 and len(r[i]) = n - 2 for every 0 <= i < n - 2, then for every i,j with 0 <= i,j < n - 2 and every a,b with 0 <= a,b < 3, r[i][j] >= grid[i + a][j + b].
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hr_len : (outMatrix r).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat) (a : Nat) (b : Nat), i < n - 2 → j < n - 2 → a < 3 → b < 3 →
      cellOf (outMatrix r) i j ≥ cellOf (matrix grid) (i + a) (j + b) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hr_len : (outMatrix r).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2), ∀ (i : Nat) (j : Nat) (a : Nat) (b : Nat), i < n - 2 → j < n - 2 → a < 3 → b < 3 →
      cellOf (outMatrix r) i j ≥ cellOf (matrix grid) (i + a) (j + b)) := by
  sorry

/-- Whenever largest_local(grid) returns a result r and r has len(r) = n - 2 and len(r[i]) = n - 2 for every 0 <= i < n - 2, then for every i,j with 0 <= i,j < n - 2, there exist a,b with 0 <= a,b < 3 such that r[i][j] = grid[i + a][j + b].
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hr_len : (outMatrix r).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      ∃ (a : Nat) (b : Nat), a < 3 ∧ b < 3 ∧
        cellOf (outMatrix r) i j = cellOf (matrix grid) (i + a) (j + b) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hr_len : (outMatrix r).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      ∃ (a : Nat) (b : Nat), a < 3 ∧ b < 3 ∧
        cellOf (outMatrix r) i j = cellOf (matrix grid) (i + a) (j + b)) := by
  sorry

/-- For every grid satisfying the preconditions, largest_local(grid) returns a result; it does not fail, overflow, or panic.
  Preconditions: Let n = len(grid). grid is square: len(grid) = n and len(grid[i]) = n for every i with 0 <= i < n. Also 3 <= n <= 100. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100) :
    ∃ (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.LargestLocal.largest_local grid = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (hgrid_len : (matrix grid).length = n)
    (hgrid_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100), ∃ (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.LargestLocal.largest_local grid = ok r) := by
  sorry

/-- Whenever largest_local(grid1) returns r1 and largest_local(grid2) returns r2, with len(r1) = len(r2) = n - 2 and all row lengths equal to n - 2, then for every i,j with 0 <= i,j < n - 2, r1[i][j] <= r2[i][j].
  Preconditions: Let n = len(grid1). grid1 and grid2 are square n by n with 3 <= n <= 100, and for every p,q with 0 <= p,q < n, grid1[p][q] <= grid2[p][q]. -/
theorem spec_7 (grid1 : Slice (alloc.vec.Vec Std.I64)) (grid2 : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h1_len : (matrix grid1).length = n)
    (h1_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid1) i).length = n)
    (h2_len : (matrix grid2).length = n)
    (h2_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid2) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hle : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix grid1) p q ≤ cellOf (matrix grid2) p q)
    (r1 : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr1 : Aegis.LargestLocal.largest_local grid1 = ok r1)
    (hr2 : Aegis.LargestLocal.largest_local grid2 = ok r2)
    (hr1_len : (outMatrix r1).length = n - 2)
    (hr2_len : (outMatrix r2).length = n - 2)
    (hr1_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r1) i).length = n - 2)
    (hr2_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r2) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix r1) i j ≤ cellOf (outMatrix r2) i j := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid1 : Slice (alloc.vec.Vec Std.I64)) (grid2 : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h1_len : (matrix grid1).length = n)
    (h1_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid1) i).length = n)
    (h2_len : (matrix grid2).length = n)
    (h2_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid2) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hle : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix grid1) p q ≤ cellOf (matrix grid2) p q)
    (r1 : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (r2 : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr1 : Aegis.LargestLocal.largest_local grid1 = ok r1)
    (hr2 : Aegis.LargestLocal.largest_local grid2 = ok r2)
    (hr1_len : (outMatrix r1).length = n - 2)
    (hr2_len : (outMatrix r2).length = n - 2)
    (hr1_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r1) i).length = n - 2)
    (hr2_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r2) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix r1) i j ≤ cellOf (outMatrix r2) i j) := by
  sorry

/-- Whenever largest_local(grid) returns r and largest_local(gridT) returns rT, with both r and rT having dimensions (n - 2) by (n - 2), then for every i,j with 0 <= i,j < n - 2, rT[i][j] = r[j][i].
  Preconditions: Let n = len(grid). grid is square n by n with 3 <= n <= 100. Define gridT[p][q] = grid[q][p] for 0 <= p,q < n. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (gridT : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hT_len : (matrix gridT).length = n)
    (hT_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridT) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hT : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridT) p q = cellOf (matrix grid) q p)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrT : Aegis.LargestLocal.largest_local gridT = ok rT)
    (hr_len : (outMatrix r).length = n - 2)
    (hrT_len : (outMatrix rT).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrT_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rT) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rT) i j = cellOf (outMatrix r) j i := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (gridT : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hT_len : (matrix gridT).length = n)
    (hT_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridT) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hT : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridT) p q = cellOf (matrix grid) q p)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrT : Aegis.LargestLocal.largest_local gridT = ok rT)
    (hr_len : (outMatrix r).length = n - 2)
    (hrT_len : (outMatrix rT).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrT_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rT) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rT) i j = cellOf (outMatrix r) j i) := by
  sorry

/-- Whenever largest_local(grid) returns r and largest_local(gridC) returns rC, with both r and rC having dimensions (n - 2) by (n - 2), then for every i,j with 0 <= i,j < n - 2, rC[i][j] = r[i][j] + c.
  Preconditions: Let n = len(grid). grid is square n by n with 3 <= n <= 100. Let c be an I64 value such that for every p,q with 0 <= p,q < n, the sum grid[p][q] + c lies in the I64 range [-2^63, 2^63 - 1]. Define gridC[p][q] = grid[p][q] + c. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (gridC : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (c : Std.I64)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hC_len : (matrix gridC).length = n)
    (hC_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridC) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hrange : ∀ (p : Nat) (q : Nat), p < n → q < n →
      -(2 : Int) ^ 63 ≤ cellOf (matrix grid) p q + c.val ∧
        cellOf (matrix grid) p q + c.val ≤ (2 : Int) ^ 63 - 1)
    (hC : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridC) p q = cellOf (matrix grid) p q + c.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rC : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrC : Aegis.LargestLocal.largest_local gridC = ok rC)
    (hr_len : (outMatrix r).length = n - 2)
    (hrC_len : (outMatrix rC).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrC_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rC) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rC) i j = cellOf (outMatrix r) i j + c.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (gridC : Slice (alloc.vec.Vec Std.I64))
    (n : Nat) (c : Std.I64)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hC_len : (matrix gridC).length = n)
    (hC_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridC) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hrange : ∀ (p : Nat) (q : Nat), p < n → q < n →
      -(2 : Int) ^ 63 ≤ cellOf (matrix grid) p q + c.val ∧
        cellOf (matrix grid) p q + c.val ≤ (2 : Int) ^ 63 - 1)
    (hC : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridC) p q = cellOf (matrix grid) p q + c.val)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rC : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrC : Aegis.LargestLocal.largest_local gridC = ok rC)
    (hr_len : (outMatrix r).length = n - 2)
    (hrC_len : (outMatrix rC).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrC_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rC) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rC) i j = cellOf (outMatrix r) i j + c.val) := by
  sorry

/-- Whenever largest_local(grid) returns r and largest_local(gridR) returns rR, with both r and rR having dimensions (n - 2) by (n - 2), then for every i,j with 0 <= i,j < n - 2, rR[i][j] = r[n - 3 - i][n - 3 - j].
  Preconditions: Let n = len(grid). grid is square n by n with 3 <= n <= 100. Define gridR[p][q] = grid[n - 1 - p][n - 1 - q] for 0 <= p,q < n. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (gridR : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hR_len : (matrix gridR).length = n)
    (hR_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridR) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hR : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridR) p q = cellOf (matrix grid) (n - 1 - p) (n - 1 - q))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rR : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrR : Aegis.LargestLocal.largest_local gridR = ok rR)
    (hr_len : (outMatrix r).length = n - 2)
    (hrR_len : (outMatrix rR).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrR_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rR) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rR) i j = cellOf (outMatrix r) (n - 3 - i) (n - 3 - j) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (gridR : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hR_len : (matrix gridR).length = n)
    (hR_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridR) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hR : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridR) p q = cellOf (matrix grid) (n - 1 - p) (n - 1 - q))
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rR : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrR : Aegis.LargestLocal.largest_local gridR = ok rR)
    (hr_len : (outMatrix r).length = n - 2)
    (hrR_len : (outMatrix rR).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrR_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rR) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rR) i j = cellOf (outMatrix r) (n - 3 - i) (n - 3 - j)) := by
  sorry

/-- Whenever largest_local(grid) returns r and largest_local(gridH) returns rH, with both r and rH having dimensions (n - 2) by (n - 2), then for every i,j with 0 <= i,j < n - 2, rH[i][j] = r[n - 3 - i][j].
  Preconditions: Let n = len(grid). grid is square n by n with 3 <= n <= 100. Define gridH[p][q] = grid[n - 1 - p][q] for 0 <= p,q < n. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (gridH : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hH_len : (matrix gridH).length = n)
    (hH_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridH) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hH : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridH) p q = cellOf (matrix grid) (n - 1 - p) q)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rH : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrH : Aegis.LargestLocal.largest_local gridH = ok rH)
    (hr_len : (outMatrix r).length = n - 2)
    (hrH_len : (outMatrix rH).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrH_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rH) i).length = n - 2) :
    ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rH) i j = cellOf (outMatrix r) (n - 3 - i) j := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (gridH : Slice (alloc.vec.Vec Std.I64))
    (n : Nat)
    (h_len : (matrix grid).length = n)
    (h_sq : ∀ (i : Nat), i < n → (rowOf (matrix grid) i).length = n)
    (hH_len : (matrix gridH).length = n)
    (hH_sq : ∀ (i : Nat), i < n → (rowOf (matrix gridH) i).length = n)
    (hn_low : 3 ≤ n) (hn_high : n ≤ 100)
    (hH : ∀ (p : Nat) (q : Nat), p < n → q < n →
      cellOf (matrix gridH) p q = cellOf (matrix grid) (n - 1 - p) q)
    (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (rH : alloc.vec.Vec (alloc.vec.Vec Std.I64))
    (hr : Aegis.LargestLocal.largest_local grid = ok r)
    (hrH : Aegis.LargestLocal.largest_local gridH = ok rH)
    (hr_len : (outMatrix r).length = n - 2)
    (hrH_len : (outMatrix rH).length = n - 2)
    (hr_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix r) i).length = n - 2)
    (hrH_sq : ∀ (i : Nat), i < n - 2 → (rowOf (outMatrix rH) i).length = n - 2), ∀ (i : Nat) (j : Nat), i < n - 2 → j < n - 2 →
      cellOf (outMatrix rH) i j = cellOf (outMatrix r) (n - 3 - i) j) := by
  sorry

end AegisSpec.LargestLocal
