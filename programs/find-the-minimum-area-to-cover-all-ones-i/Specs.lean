import Aegis.MinimumArea.Code.Funs

/-!
# Specifications of `Aegis.MinimumArea.minimum_area`

LeetCode problem `find-the-minimum-area-to-cover-all-ones-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumArea

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def listMinI (l : List Nat) (d : Int) : Int :=
  l.foldr (fun x acc => min (x : Int) acc) d

def listMaxI (l : List Nat) (d : Int) : Int :=
  l.foldr (fun x acc => max (x : Int) acc) d

def oneRows (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : List Nat :=
  (List.range m).filter (fun i => (List.range n).any (fun j => decide (cell grid i j = 1)))

def oneCols (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : List Nat :=
  (List.range n).filter (fun j => (List.range m).any (fun i => decide (cell grid i j = 1)))

def Rmin (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  listMinI (oneRows grid m n) (m : Int)

def Rmax (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  listMaxI (oneRows grid m n) (-1)

def Cmin (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  listMinI (oneCols grid m n) (n : Int)

def Cmax (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  listMaxI (oneCols grid m n) (-1)

/-- Whenever the function returns a result r, r = (Rmax - Rmin + 1) * (Cmax - Cmin + 1), where Rmin is the minimum row index i such that some cell (i,j) equals 1, Rmax is the maximum such row index, Cmin is the minimum column index j such that some cell (i,j) equals 1, and Cmax is the maximum such column index.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val = (Rmax grid m n - Rmin grid m n + 1) * (Cmax grid m n - Cmin grid m n + 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val = (Rmax grid m n - Rmin grid m n + 1) * (Cmax grid m n - Cmin grid m n + 1)) := by
  sorry

/-- The function returns a result r; in particular, it does not panic, access out of bounds, or overflow a 64-bit integer.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1) :
    ∃ r : Std.I64, Aegis.MinimumArea.minimum_area grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1), ∃ r : Std.I64, Aegis.MinimumArea.minimum_area grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= m * n.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val ≤ (m : Int) * (n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val ≤ (m : Int) * (n : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exist integers r1,r2,c1,c2 with 0 <= r1 <= r2 < m and 0 <= c1 <= c2 < n such that every 1-cell (i,j) satisfies r1 <= i <= r2 and c1 <= j <= c2, and r = (r2 - r1 + 1) * (c2 - c1 + 1).
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    ∃ r1 r2 c1 c2 : Int,
      0 ≤ r1 ∧ r1 ≤ r2 ∧ r2 < (m : Int) ∧ 0 ≤ c1 ∧ c1 ≤ c2 ∧ c2 < (n : Int) ∧
        (∀ i j, i < m → j < n → cell grid i j = 1 →
          r1 ≤ (i : Int) ∧ (i : Int) ≤ r2 ∧ c1 ≤ (j : Int) ∧ (j : Int) ≤ c2) ∧
        r.val = (r2 - r1 + 1) * (c2 - c1 + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), ∃ r1 r2 c1 c2 : Int,
      0 ≤ r1 ∧ r1 ≤ r2 ∧ r2 < (m : Int) ∧ 0 ≤ c1 ∧ c1 ≤ c2 ∧ c2 < (n : Int) ∧
        (∀ i j, i < m → j < n → cell grid i j = 1 →
          r1 ≤ (i : Int) ∧ (i : Int) ≤ r2 ∧ c1 ≤ (j : Int) ∧ (j : Int) ≤ c2) ∧
        r.val = (r2 - r1 + 1) * (c2 - c1 + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every choice of integers r1,r2,c1,c2 with 0 <= r1 <= r2 < m and 0 <= c1 <= c2 < n, if every 1-cell (i,j) satisfies r1 <= i <= r2 and c1 <= j <= c2, then r <= (r2 - r1 + 1) * (c2 - c1 + 1).
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    ∀ r1 r2 c1 c2 : Int,
      0 ≤ r1 → r1 ≤ r2 → r2 < (m : Int) → 0 ≤ c1 → c1 ≤ c2 → c2 < (n : Int) →
        (∀ i j, i < m → j < n → cell grid i j = 1 →
          r1 ≤ (i : Int) ∧ (i : Int) ≤ r2 ∧ c1 ≤ (j : Int) ∧ (j : Int) ≤ c2) →
        r.val ≤ (r2 - r1 + 1) * (c2 - c1 + 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), ∀ r1 r2 c1 c2 : Int,
      0 ≤ r1 → r1 ≤ r2 → r2 < (m : Int) → 0 ≤ c1 → c1 ≤ c2 → c2 < (n : Int) →
        (∀ i j, i < m → j < n → cell grid i j = 1 →
          r1 ≤ (i : Int) ∧ (i : Int) ≤ r2 ∧ c1 ≤ (j : Int) ∧ (j : Int) ≤ c2) →
        r.val ≤ (r2 - r1 + 1) * (c2 - c1 + 1)) := by
  sorry

/-- Whenever the function returns a result r, for every two 1-cells (i1,j1) and (i2,j2), possibly equal, r >= (abs(i1 - i2) + 1) * (abs(j1 - j2) + 1).
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    ∀ i1 j1 i2 j2 : Nat,
      i1 < m → j1 < n → i2 < m → j2 < n →
        cell grid i1 j1 = 1 → cell grid i2 j2 = 1 →
        (|(i1 : Int) - (i2 : Int)| + 1) * (|(j1 : Int) - (j2 : Int)| + 1) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), ∀ i1 j1 i2 j2 : Nat,
      i1 < m → j1 < n → i2 < m → j2 < n →
        cell grid i1 j1 = 1 → cell grid i2 j2 = 1 →
        (|(i1 : Int) - (i2 : Int)| + 1) * (|(j1 : Int) - (j2 : Int)| + 1) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = Cmax - Cmin + 1, where Cmin is the minimum column index of a 1-cell and Cmax is the maximum column index of a 1-cell.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. Suppose all 1-cells have the same row index. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hsameRow : ∃ i0, ∀ i j, i < m → j < n → cell grid i j = 1 → i = i0)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val = Cmax grid m n - Cmin grid m n + 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hsameRow : ∃ i0, ∀ i j, i < m → j < n → cell grid i j = 1 → i = i0)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val = Cmax grid m n - Cmin grid m n + 1) := by
  sorry

/-- Whenever the function returns a result r, r = Rmax - Rmin + 1, where Rmin is the minimum row index of a 1-cell and Rmax is the maximum row index of a 1-cell.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. Suppose all 1-cells have the same column index. -/
theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hsameCol : ∃ j0, ∀ i j, i < m → j < n → cell grid i j = 1 → j = j0)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val = Rmax grid m n - Rmin grid m n + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hsameCol : ∃ j0, ∀ i j, i < m → j < n → cell grid i j = 1 → j = j0)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val = Rmax grid m n - Rmin grid m n + 1) := by
  sorry

/-- If there is at least one 1 in row 0, at least one 1 in row m - 1, at least one 1 in column 0, and at least one 1 in column n - 1, then whenever the function returns a result r, r = m * n.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hfirstRow : ∃ j, j < n ∧ cell grid 0 j = 1)
    (hlastRow : ∃ j, j < n ∧ cell grid (m - 1) j = 1)
    (hfirstCol : ∃ i, i < m ∧ cell grid i 0 = 1)
    (hlastCol : ∃ i, i < m ∧ cell grid i (n - 1) = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val = (m : Int) * (n : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hfirstRow : ∃ j, j < n ∧ cell grid 0 j = 1)
    (hlastRow : ∃ j, j < n ∧ cell grid (m - 1) j = 1)
    (hfirstCol : ∃ i, i < m ∧ cell grid i 0 = 1)
    (hlastCol : ∃ i, i < m ∧ cell grid i (n - 1) = 1)
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val = (m : Int) * (n : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = (abs(i1 - i2) + 1) * (abs(j1 - j2) + 1).
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. Suppose exactly two distinct cells equal 1, namely (i1,j1) and (i2,j2). -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (i1 j1 i2 j2 : Nat)
    (hb1 : i1 < m ∧ j1 < n) (hb2 : i2 < m ∧ j2 < n)
    (hne : (i1, j1) ≠ (i2, j2))
    (hexactly : ∀ i j, i < m → j < n →
      (cell grid i j = 1 ↔ ((i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2))))
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r) :
    r.val = (|(i1 : Int) - (i2 : Int)| + 1) * (|(j1 : Int) - (j2 : Int)| + 1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (i1 j1 i2 j2 : Nat)
    (hb1 : i1 < m ∧ j1 < n) (hb2 : i2 < m ∧ j2 < n)
    (hne : (i1, j1) ≠ (i2, j2))
    (hexactly : ∀ i j, i < m → j < n →
      (cell grid i j = 1 ↔ ((i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2))))
    (r : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r), r.val = (|(i1 : Int) - (i2 : Int)| + 1) * (|(j1 : Int) - (j2 : Int)| + 1)) := by
  sorry

/-- Whenever the function returns a result r for grid and returns a result rT for gridT, r = rT.
  Preconditions: Let m = len(grid) and let n be the common row length. Assume 1 <= m <= 1000, 1 <= n <= 1000, every row of grid has length n, every grid[i][j] is either 0 or 1 for 0 <= i < m and 0 <= j < n, and there is at least one cell with value 1. Let gridT be the n by m grid defined by gridT[j][i] = grid[i][j]. -/
theorem spec_12 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hTrows : gridT.val.length = n)
    (hTwidth : ∀ row ∈ gridT.val, row.val.length = m)
    (hT : rows gridT = (rows grid).transpose)
    (r rT : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r)
    (hrT : Aegis.MinimumArea.minimum_area gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hrows : grid.val.length = m)
    (hwidth : ∀ row ∈ grid.val, row.val.length = n)
    (hbinary : ∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)
    (hone : ∃ i j, i < m ∧ j < n ∧ cell grid i j = 1)
    (hTrows : gridT.val.length = n)
    (hTwidth : ∀ row ∈ gridT.val, row.val.length = m)
    (hT : rows gridT = (rows grid).transpose)
    (r rT : Std.I64) (hr : Aegis.MinimumArea.minimum_area grid = ok r)
    (hrT : Aegis.MinimumArea.minimum_area gridT = ok rT), r.val = rT.val) := by
  sorry

/-- Whenever the function returns a result rA for A and a result rB for B, rA <= rB.
  Preconditions: Let m = len(grid) and let n be the common row length. Consider two valid binary grids A and B of the same dimensions m and n, each with every entry 0 or 1 and at least one 1, and suppose that for every 0 <= i < m and 0 <= j < n, A[i][j] = 1 implies B[i][j] = 1. -/
theorem spec_13 (A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hArows : A.val.length = m)
    (hAwidth : ∀ row ∈ A.val, row.val.length = n)
    (hAbinary : ∀ i j, i < m → j < n → cell A i j = 0 ∨ cell A i j = 1)
    (hAone : ∃ i j, i < m ∧ j < n ∧ cell A i j = 1)
    (hBrows : B.val.length = m)
    (hBwidth : ∀ row ∈ B.val, row.val.length = n)
    (hBbinary : ∀ i j, i < m → j < n → cell B i j = 0 ∨ cell B i j = 1)
    (hBone : ∃ i j, i < m ∧ j < n ∧ cell B i j = 1)
    (hmono : ∀ i j, i < m → j < n → cell A i j = 1 → cell B i j = 1)
    (rA rB : Std.I64) (hrA : Aegis.MinimumArea.minimum_area A = ok rA)
    (hrB : Aegis.MinimumArea.minimum_area B = ok rB) :
    rA.val ≤ rB.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
    (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
    (hArows : A.val.length = m)
    (hAwidth : ∀ row ∈ A.val, row.val.length = n)
    (hAbinary : ∀ i j, i < m → j < n → cell A i j = 0 ∨ cell A i j = 1)
    (hAone : ∃ i j, i < m ∧ j < n ∧ cell A i j = 1)
    (hBrows : B.val.length = m)
    (hBwidth : ∀ row ∈ B.val, row.val.length = n)
    (hBbinary : ∀ i j, i < m → j < n → cell B i j = 0 ∨ cell B i j = 1)
    (hBone : ∃ i j, i < m ∧ j < n ∧ cell B i j = 1)
    (hmono : ∀ i j, i < m → j < n → cell A i j = 1 → cell B i j = 1)
    (rA rB : Std.I64) (hrA : Aegis.MinimumArea.minimum_area A = ok rA)
    (hrB : Aegis.MinimumArea.minimum_area B = ok rB), rA.val ≤ rB.val) := by
  sorry

end AegisSpec.MinimumArea
