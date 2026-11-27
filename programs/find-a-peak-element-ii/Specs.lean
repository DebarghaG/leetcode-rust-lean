import Aegis.FindPeakGrid.Code.Funs

/-!
# Specifications of `Aegis.FindPeakGrid.find_peak_grid`

LeetCode problem `find-a-peak-element-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindPeakGrid (find_peak_grid)
set_option autoImplicit false

namespace AegisSpec.FindPeakGrid

def rowValues (mat : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Int :=
  match mat.val[i]? with
  | none => []
  | some row => row.val.map (fun v => v.val)

def cell (mat : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ((rowValues mat i)[j]?).getD 0

def manhattan (x y i j : Nat) : Nat :=
  (max x i - min x i) + (max y j - min y j)

def IsPeak (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (i j : Nat) : Prop :=
  i < m ∧ j < n ∧
    ∀ x y : Nat, x < m → y < n → manhattan x y i j = 1 → cell mat x y < cell mat i j

structure ValidGrid (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop where

  m_eq : mat.val.length = m

  m_pos : 1 ≤ m

  m_le : m ≤ 500

  n_pos : 1 ≤ n

  n_le : n ≤ 500

  row_len : ∀ i : Nat, i < m → (rowValues mat i).length = n

  entry_bounds : ∀ i j : Nat, i < m → j < n → 1 ≤ cell mat i j ∧ cell mat i j ≤ 100000

  horiz_ne : ∀ i j : Nat, i < m → j + 1 < n → cell mat i j ≠ cell mat i (j + 1)

  vert_ne : ∀ i j : Nat, i + 1 < m → j < n → cell mat i j ≠ cell mat (i + 1) j

/-- Whenever find_peak_grid(mat) returns a result r, len(r) = 2, and, writing i = r[0] and j = r[1] as mathematical integers, 0 <= i < m, 0 <= j < n, and mat[i][j] is a peak of mat: for every x,y with 0 <= x < m, 0 <= y < n and |x - i| + |y - j| = 1, we have mat[i][j] > mat[x][y]. Equivalently, mat[i][j] is strictly greater than every existing orthogonal neighbor; boundary cells automatically exceed the outside sentinel -1 because every mat value is positive.
  Preconditions: Let m = len(mat). The input satisfies: 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that every row mat[i] has length n, so mat is an m x n rectangular grid; for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= mat[i][j] <= 100000; for every i with 0 <= i < m and every j with 0 <= j+1 < n, mat[i][j] != mat[i][j+1]; and for every i with 0 <= i+1 < m and every j with 0 <= j < n, mat[i][j] != mat[i+1][j]. -/
theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : ValidGrid mat m n) :
    ∀ r : alloc.vec.Vec Std.I64, find_peak_grid mat = ok r →
      r.val.length = 2 ∧
        ∃ i j : Nat, r.val.map (fun v => v.val) = [↑i, ↑j] ∧ IsPeak mat m n i j := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : ValidGrid mat m n), ∀ r : alloc.vec.Vec Std.I64, find_peak_grid mat = ok r →
      r.val.length = 2 ∧
        ∃ i j : Nat, r.val.map (fun v => v.val) = [↑i, ↑j] ∧ IsPeak mat m n i j) := by
  sorry

/-- For every input satisfying the preconditions, find_peak_grid(mat) returns a result r; it does not fail, panic, overflow, or access an index out of bounds.
  Preconditions: Let m = len(mat). The input satisfies: 1 <= m <= 500; there is an integer n with 1 <= n <= 500 such that every row mat[i] has length n, so mat is an m x n rectangular grid; for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= mat[i][j] <= 100000; for every i with 0 <= i < m and every j with 0 <= j+1 < n, mat[i][j] != mat[i][j+1]; and for every i with 0 <= i+1 < m and every j with 0 <= j < n, mat[i][j] != mat[i+1][j]. -/
theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : ValidGrid mat m n) :
    ∃ r : alloc.vec.Vec Std.I64, find_peak_grid mat = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (h : ValidGrid mat m n), ∃ r : alloc.vec.Vec Std.I64, find_peak_grid mat = ok r) := by
  sorry

def halvingIters : Nat → Nat
  | 0 => 0
  | len + 1 => halvingIters ((len + 1) / 2) + 1

def workEstimate (m n : Nat) : Nat :=
  halvingIters (m - 1) * (n + 3) + n

end AegisSpec.FindPeakGrid
