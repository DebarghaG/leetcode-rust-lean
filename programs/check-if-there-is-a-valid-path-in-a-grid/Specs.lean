import Aegis.HasValidPath.Code.Funs

/-!
# Specifications of `Aegis.HasValidPath.has_valid_path`

LeetCode problem `check-if-there-is-a-valid-path-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasValidPath

open Aegis.HasValidPath

def rowsOf (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  (rowsOf grid).length

def numCols (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
  match rowsOf grid with
  | [] => 0
  | row :: _ => row.length

def cellVal (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match (rowsOf grid)[i]? with
  | none => 0
  | some row => (row[j]?).getD 0

abbrev opensLeft (t : Int) : Prop := t = 1 ∨ t = 3 ∨ t = 5

abbrev opensRight (t : Int) : Prop := t = 1 ∨ t = 4 ∨ t = 6

abbrev opensUp (t : Int) : Prop := t = 2 ∨ t = 5 ∨ t = 6

abbrev opensDown (t : Int) : Prop := t = 2 ∨ t = 3 ∨ t = 4

def InGrid (grid : Slice (alloc.vec.Vec Std.I64)) (p : Nat × Nat) : Prop :=
  p.1 < numRows grid ∧ p.2 < numCols grid

def Step (grid : Slice (alloc.vec.Vec Std.I64)) (p q : Nat × Nat) : Prop :=
  InGrid grid p ∧ InGrid grid q ∧
    ((p.1 = q.1 ∧ p.2 + 1 = q.2 ∧
        opensRight (cellVal grid p.1 p.2) ∧ opensLeft (cellVal grid q.1 q.2)) ∨
     (p.1 = q.1 ∧ q.2 + 1 = p.2 ∧
        opensRight (cellVal grid q.1 q.2) ∧ opensLeft (cellVal grid p.1 p.2)) ∨
     (p.2 = q.2 ∧ p.1 + 1 = q.1 ∧
        opensDown (cellVal grid p.1 p.2) ∧ opensUp (cellVal grid q.1 q.2)) ∨
     (p.2 = q.2 ∧ q.1 + 1 = p.1 ∧
        opensDown (cellVal grid q.1 q.2) ∧ opensUp (cellVal grid p.1 p.2)))

def Connected (grid : Slice (alloc.vec.Vec Std.I64)) (p q : Nat × Nat) : Prop :=
  Relation.ReflTransGen (Step grid) p q

def Steps (grid : Slice (alloc.vec.Vec Std.I64)) : List (Nat × Nat) → Prop
  | [] => True
  | [_] => True
  | p :: q :: rest => Step grid p q ∧ Steps grid (q :: rest)

def IsStreetPath (grid : Slice (alloc.vec.Vec Std.I64)) (start goal : Nat × Nat)
    (path : List (Nat × Nat)) : Prop :=
  path.head? = some start ∧ path.getLast? = some goal ∧ path.Nodup ∧
    (∀ p ∈ path, InGrid grid p) ∧ Steps grid path

def rotT : Int → Int
  | 1 => 2
  | 2 => 1
  | 3 => 6
  | 4 => 4
  | 5 => 5
  | 6 => 3
  | t => t

def rotU : Int → Int
  | 1 => 1
  | 2 => 2
  | 3 => 6
  | 4 => 5
  | 5 => 4
  | 6 => 3
  | t => t

def transposeRows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  (List.range (numCols grid)).map fun i =>
    (List.range (numRows grid)).map fun j => rotT (cellVal grid j i)

def rotate180Rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  (List.range (numRows grid)).map fun i =>
    (List.range (numCols grid)).map fun j =>
      rotU (cellVal grid (numRows grid - 1 - i) (numCols grid - 1 - j))

/-- Whenever has_valid_path(grid) returns a result r, r is true if and only if (0,0) and (m-1,n-1) lie in the same connected component of the undirected graph whose vertices are all pairs (i,j) with 0 <= i < m and 0 <= j < n and whose edges join exactly those orthogonally adjacent vertices (|i-i'| + |j-j'| = 1) whose streets open toward each other. A cell opens left iff its value is in {1,3,5}, opens right iff its value is in {1,4,6}, opens up iff its value is in {2,5,6}, and opens down iff its value is in {2,3,4}. Coordinates are 0-based.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r) :
    (r = true ↔ Connected grid (0, 0) (numRows grid - 1, numCols grid - 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r), (r = true ↔ Connected grid (0, 0) (numRows grid - 1, numCols grid - 1))) := by
  sorry

/-- has_valid_path(grid) returns some result r; it does not fail, overflow, access out of bounds, or panic.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6) :
    ∃ r, has_valid_path grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6), ∃ r, has_valid_path grid = ok r) := by
  sorry

/-- Whenever has_valid_path(grid) returns a result r, r = true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m = 1, n = 1, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : numRows grid = 1) (hn : numCols grid = 1)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r) :
    r = true := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : numRows grid = 1) (hn : numCols grid = 1)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r), r = true) := by
  sorry

/-- Whenever has_valid_path(grid) returns a result r, r = true if and only if for every j with 0 <= j < n-1, grid[0][j] opens right (its value is in {1,4,6}) and grid[0][j+1] opens left (its value is in {1,3,5}). For n = 1 the universal condition is vacuously true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m = 1, n >= 1, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : numRows grid = 1) (hn : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r) :
    (r = true ↔ ∀ j, j < numCols grid - 1 →
      opensRight (cellVal grid 0 j) ∧ opensLeft (cellVal grid 0 (j + 1))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : numRows grid = 1) (hn : 1 ≤ numCols grid) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r), (r = true ↔ ∀ j, j < numCols grid - 1 →
      opensRight (cellVal grid 0 j) ∧ opensLeft (cellVal grid 0 (j + 1)))) := by
  sorry

/-- Whenever has_valid_path(grid) returns a result r, r = true if and only if for every i with 0 <= i < m-1, grid[i][0] opens down (its value is in {2,3,4}) and grid[i+1][0] opens up (its value is in {2,5,6}). For m = 1 the universal condition is vacuously true.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume n = 1, m >= 1, m <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64))
    (hn : numCols grid = 1) (hm : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r) :
    (r = true ↔ ∀ i, i < numRows grid - 1 →
      opensDown (cellVal grid i 0) ∧ opensUp (cellVal grid (i + 1) 0)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hn : numCols grid = 1) (hm : 1 ≤ numRows grid) (hm_le : numRows grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (r : Bool) (hr : has_valid_path grid = ok r), (r = true ↔ ∀ i, i < numRows grid - 1 →
      opensDown (cellVal grid i 0) ∧ opensUp (cellVal grid (i + 1) 0))) := by
  sorry

/-- If (n = 1 or grid[0][0] is not in {1,4,6}) and (m = 1 or grid[0][0] is not in {2,3,4}), then whenever has_valid_path(grid) returns a result r, r = false.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, m > 1 or n > 1, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hne : 1 < numRows grid ∨ 1 < numCols grid)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hright : numCols grid = 1 ∨ ¬ opensRight (cellVal grid 0 0))
    (hdown : numRows grid = 1 ∨ ¬ opensDown (cellVal grid 0 0))
    (r : Bool) (hr : has_valid_path grid = ok r) :
    r = false := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hne : 1 < numRows grid ∨ 1 < numCols grid)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hright : numCols grid = 1 ∨ ¬ opensRight (cellVal grid 0 0))
    (hdown : numRows grid = 1 ∨ ¬ opensDown (cellVal grid 0 0))
    (r : Bool) (hr : has_valid_path grid = ok r), r = false) := by
  sorry

/-- If (n = 1 or grid[m-1][n-1] is not in {1,3,5}) and (m = 1 or grid[m-1][n-1] is not in {2,5,6}), then whenever has_valid_path(grid) returns a result r, r = false.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, m > 1 or n > 1, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hne : 1 < numRows grid ∨ 1 < numCols grid)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hleft : numCols grid = 1 ∨
      ¬ opensLeft (cellVal grid (numRows grid - 1) (numCols grid - 1)))
    (hup : numRows grid = 1 ∨
      ¬ opensUp (cellVal grid (numRows grid - 1) (numCols grid - 1)))
    (r : Bool) (hr : has_valid_path grid = ok r) :
    r = false := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hne : 1 < numRows grid ∨ 1 < numCols grid)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hleft : numCols grid = 1 ∨
      ¬ opensLeft (cellVal grid (numRows grid - 1) (numCols grid - 1)))
    (hup : numRows grid = 1 ∨
      ¬ opensUp (cellVal grid (numRows grid - 1) (numCols grid - 1)))
    (r : Bool) (hr : has_valid_path grid = ok r), r = false) := by
  sorry

/-- Whenever has_valid_path(grid) returns true, there exists a valid street-following path from (0,0) to (m-1,n-1), with no repeated cells, having k steps where 0 <= k <= m*n - 1. A street-following path is a sequence of orthogonally adjacent cells in the grid where each consecutive pair is mutually connected by the opening sets left {1,3,5}, right {1,4,6}, up {2,5,6}, down {2,3,4}.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hr : has_valid_path grid = ok true) :
    ∃ (path : List (Nat × Nat)) (k : Nat),
      IsStreetPath grid (0, 0) (numRows grid - 1, numCols grid - 1) path ∧
        path.length = k + 1 ∧ k ≤ numRows grid * numCols grid - 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hr : has_valid_path grid = ok true), ∃ (path : List (Nat × Nat)) (k : Nat),
      IsStreetPath grid (0, 0) (numRows grid - 1, numCols grid - 1) path ∧
        path.length = k + 1 ∧ k ≤ numRows grid * numCols grid - 1) := by
  sorry

/-- Let G' be the n by m grid defined by G'[i][j] = t(grid[j][i]) for 0 <= i < n and 0 <= j < m, where t(1)=2, t(2)=1, t(3)=6, t(4)=4, t(5)=5, t(6)=3. Whenever has_valid_path(grid) returns r and has_valid_path(G') returns r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hG' : rowsOf grid' = transposeRows grid)
    (r r' : Bool)
    (hr : has_valid_path grid = ok r) (hr' : has_valid_path grid' = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hG' : rowsOf grid' = transposeRows grid)
    (r r' : Bool)
    (hr : has_valid_path grid = ok r) (hr' : has_valid_path grid' = ok r'), r = r') := by
  sorry

/-- Let G' be the m by n grid defined by G'[i][j] = u(grid[m-1-i][n-1-j]) for 0 <= i < m and 0 <= j < n, where u(1)=1, u(2)=2, u(3)=6, u(4)=5, u(5)=4, u(6)=3. Whenever has_valid_path(grid) returns r and has_valid_path(G') returns r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m <= 300, n <= 300, every row of grid has length n, and for every i,j with 0 <= i < m and 0 <= j < n, 1 <= grid[i][j] <= 6. -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hG' : rowsOf grid' = rotate180Rows grid)
    (r r' : Bool)
    (hr : has_valid_path grid = ok r) (hr' : has_valid_path grid' = ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64))
    (hm : 1 ≤ numRows grid) (hn : 1 ≤ numCols grid)
    (hm_le : numRows grid ≤ 300) (hn_le : numCols grid ≤ 300)
    (hrows : ∀ row ∈ rowsOf grid, row.length = numCols grid)
    (hval : ∀ i j, i < numRows grid → j < numCols grid →
      1 ≤ cellVal grid i j ∧ cellVal grid i j ≤ 6)
    (hG' : rowsOf grid' = rotate180Rows grid)
    (r r' : Bool)
    (hr : has_valid_path grid = ok r) (hr' : has_valid_path grid' = ok r'), r = r') := by
  sorry

end AegisSpec.HasValidPath
