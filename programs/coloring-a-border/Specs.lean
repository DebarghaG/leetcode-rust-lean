import Aegis.ColorBorder.Code.Funs

/-!
# Specifications of `Aegis.ColorBorder.color_border`

LeetCode problem `coloring-a-border`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ColorBorder

def rowLen (rows : List (alloc.vec.Vec I64)) (i : Nat) : Nat :=
  ((rows[i]?).map (fun row => row.val.length)).getD 0

def cellVal (rows : List (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  ((rows[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))).getD 0

def startVal (grid : Slice (alloc.vec.Vec I64)) (row col : I64) : Int :=
  cellVal grid.val row.val.toNat col.val.toNat

def Adjacent (p q : Nat × Nat) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
    (p.2 + 1 = q.2 ∧ p.1 = q.1) ∨ (q.2 + 1 = p.2 ∧ p.1 = q.1)

def PathStep (grid : Slice (alloc.vec.Vec I64)) (c0 : Int) (m n : Nat)
    (p q : Nat × Nat) : Prop :=
  p.1 < m ∧ p.2 < n ∧ q.1 < m ∧ q.2 < n ∧
    cellVal grid.val p.1 p.2 = c0 ∧ cellVal grid.val q.1 q.2 = c0 ∧ Adjacent p q

def InC (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (row col : I64)
    (i j : Nat) : Prop :=
  i < m ∧ j < n ∧ cellVal grid.val i j = startVal grid row col ∧
    Relation.ReflTransGen (PathStep grid (startVal grid row col) m n)
      (row.val.toNat, col.val.toNat) (i, j)

def InB (grid : Slice (alloc.vec.Vec I64)) (m n : Nat) (row col : I64)
    (i j : Nat) : Prop :=
  InC grid m n row col i j ∧
    (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1 ∨
      (1 ≤ i ∧ ¬ InC grid m n row col (i - 1) j) ∨
      (i + 1 < m ∧ ¬ InC grid m n row col (i + 1) j) ∨
      (1 ≤ j ∧ ¬ InC grid m n row col i (j - 1)) ∨
      (j + 1 < n ∧ ¬ InC grid m n row col i (j + 1)))

def InteriorSameVal (rows : List (alloc.vec.Vec I64)) (m n i j : Nat) : Prop :=
  1 ≤ i ∧ i + 1 < m ∧ 1 ≤ j ∧ j + 1 < n ∧
    cellVal rows (i - 1) j = cellVal rows i j ∧
    cellVal rows (i + 1) j = cellVal rows i j ∧
    cellVal rows i (j - 1) = cellVal rows i j ∧
    cellVal rows i (j + 1) = cellVal rows i j

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. Let B be the set of (i,j) in C such that i = 0 or i = m-1 or j = 0 or j = n-1, or at least one of the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) lies in the grid and is not in C. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n, if (i,j) is in B then r[i][j] = color, and if (i,j) is not in B then r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          (InB grid m n row col i j → cellVal r.val i j = color.val) ∧
            (¬ InB grid m n row col i j → cellVal r.val i j = cellVal grid.val i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          (InB grid m n row col i j → cellVal r.val i j = color.val) ∧
            (¬ InB grid m n row col i j → cellVal r.val i j = cellVal grid.val i j)) := by
  sorry

/-- The function returns a result r with len(r) = m and for every i with 0 <= i < m, len(r[i]) = n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧ ∀ i, i < m → rowLen r.val i = n := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧ ∀ i, i < m → rowLen r.val i = n) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n, if (i,j) is not in C then r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          ¬ InC grid m n row col i j → cellVal r.val i j = cellVal grid.val i j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          ¬ InC grid m n row col i j → cellVal r.val i j = cellVal grid.val i j) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. Let B be the set of (i,j) in C such that i = 0 or i = m-1 or j = 0 or j = n-1, or at least one of the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) lies in the grid and is not in C. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every (i,j) in B, r[i][j] = color.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n → InB grid m n row col i j → cellVal r.val i j = color.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n → InB grid m n row col i j → cellVal r.val i j = color.val) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. Let B be the set of (i,j) in C such that i = 0 or i = m-1 or j = 0 or j = n-1, or at least one of the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) lies in the grid and is not in C. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n, if (i,j) is in C and (i,j) is not in B then r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          InC grid m n row col i j → ¬ InB grid m n row col i j →
            cellVal r.val i j = cellVal grid.val i j := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n →
          InC grid m n row col i j → ¬ InB grid m n row col i j →
            cellVal r.val i j = cellVal grid.val i j) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or perform an out-of-bounds access.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r) := by
  sorry

/-- The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. If color = grid[row][col], then for every i, j with 0 <= i < m and 0 <= j < n, r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        (color.val = startVal grid row col →
          ∀ i j, i < m → j < n → cellVal r.val i j = cellVal grid.val i j) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        (color.val = startVal grid row col →
          ∀ i j, i < m → j < n → cellVal r.val i j = cellVal grid.val i j)) := by
  sorry

/-- The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. If every cell satisfies grid[i][j] = grid[row][col], then for every i, j with 0 <= i < m and 0 <= j < n, r[i][j] = color when i = 0 or i = m-1 or j = 0 or j = n-1, and r[i][j] = grid[i][j] otherwise.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ((∀ i j, i < m → j < n → cellVal grid.val i j = startVal grid row col) →
          ∀ i j, i < m → j < n →
            (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1 → cellVal r.val i j = color.val) ∧
              (¬ (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1) →
                cellVal r.val i j = cellVal grid.val i j)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ((∀ i j, i < m → j < n → cellVal grid.val i j = startVal grid row col) →
          ∀ i j, i < m → j < n →
            (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1 → cellVal r.val i j = color.val) ∧
              (¬ (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1) →
                cellVal r.val i j = cellVal grid.val i j))) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. Let B be the set of (i,j) in C such that i = 0 or i = m-1 or j = 0 or j = n-1, or at least one of the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) lies in the grid and is not in C. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. If color != grid[row][col], then for every i, j with 0 <= i < m and 0 <= j < n, r[i][j] != grid[i][j] if and only if (i,j) is in B.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_9
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        (color.val ≠ startVal grid row col →
          ∀ i j, i < m → j < n →
            (cellVal r.val i j ≠ cellVal grid.val i j ↔ InB grid m n row col i j)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        (color.val ≠ startVal grid row col →
          ∀ i j, i < m → j < n →
            (cellVal r.val i j ≠ cellVal grid.val i j ↔ InB grid m n row col i j))) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every (i,j) in C, if (i,j) is on the grid boundary or one of the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) lies in the grid and has value different from grid[i][j], then r[i][j] = color.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_10
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, InC grid m n row col i j →
          (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1 ∨
              (1 ≤ i ∧ cellVal grid.val (i - 1) j ≠ cellVal grid.val i j) ∨
              (i + 1 < m ∧ cellVal grid.val (i + 1) j ≠ cellVal grid.val i j) ∨
              (1 ≤ j ∧ cellVal grid.val i (j - 1) ≠ cellVal grid.val i j) ∨
              (j + 1 < n ∧ cellVal grid.val i (j + 1) ≠ cellVal grid.val i j)) →
            cellVal r.val i j = color.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, InC grid m n row col i j →
          (i = 0 ∨ i = m - 1 ∨ j = 0 ∨ j = n - 1 ∨
              (1 ≤ i ∧ cellVal grid.val (i - 1) j ≠ cellVal grid.val i j) ∨
              (i + 1 < m ∧ cellVal grid.val (i + 1) j ≠ cellVal grid.val i j) ∨
              (1 ≤ j ∧ cellVal grid.val i (j - 1) ≠ cellVal grid.val i j) ∨
              (j + 1 < n ∧ cellVal grid.val i (j + 1) ≠ cellVal grid.val i j)) →
            cellVal r.val i j = color.val) := by
  sorry

/-- Let c0 = grid[row][col]. Let C be the set of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = c0, and there is a finite sequence of grid cells starting at (row,col) and ending at (i,j), with each consecutive pair differing by exactly one step up, down, left, or right, and every cell in the sequence having value c0. The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every (i,j) in C such that 0 < i < m-1 and 0 < j < n-1, if the four neighbors (i-1,j), (i+1,j), (i,j-1), (i,j+1) all lie in the grid and all have grid value equal to grid[i][j], then r[i][j] = grid[i][j].
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_11
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, InC grid m n row col i j → 0 < i → i < m - 1 → 0 < j → j < n - 1 →
          InteriorSameVal grid.val m n i j → cellVal r.val i j = cellVal grid.val i j := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, InC grid m n row col i j → 0 < i → i < m - 1 → 0 < j → j < n - 1 →
          InteriorSameVal grid.val m n i j → cellVal r.val i j = cellVal grid.val i j) := by
  sorry

/-- The function returns a result r with len(r) = m and len(r[i]) = n for every i with 0 <= i < m. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= r[i][j] <= 1000.
  Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies m >= 1, n >= 1, for every i with 0 <= i < m len(grid[i]) = n, 0 <= row < m, 0 <= col < n, for every i, j with 0 <= i < m and 0 <= j < n 1 <= grid[i][j] <= 1000, and 1 <= color <= 1000. -/
theorem spec_12
    (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n → 1 ≤ cellVal r.val i j ∧ cellVal r.val i j ≤ 1000 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col color : I64) (m n : Nat)
    (hm : m = grid.val.length) (hn : n = rowLen grid.val 0)
    (hm1 : 1 ≤ m) (hn1 : 1 ≤ n)
    (hrows : ∀ i, i < m → rowLen grid.val i = n)
    (hrow_nn : 0 ≤ row.val) (hrow_lt : row.val < (m : Int))
    (hcol_nn : 0 ≤ col.val) (hcol_lt : col.val < (n : Int))
    (hcells : ∀ i j, i < m → j < n →
      1 ≤ cellVal grid.val i j ∧ cellVal grid.val i j ≤ 1000)
    (hcolor : 1 ≤ color.val ∧ color.val ≤ 1000), ∃ r : alloc.vec.Vec (alloc.vec.Vec I64),
      Aegis.ColorBorder.color_border grid row col color = ok r ∧
        r.val.length = m ∧
        (∀ i, i < m → rowLen r.val i = n) ∧
        ∀ i j, i < m → j < n → 1 ≤ cellVal r.val i j ∧ cellVal r.val i j ≤ 1000) := by
  sorry

end AegisSpec.ColorBorder
