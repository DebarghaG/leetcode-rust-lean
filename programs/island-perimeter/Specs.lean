import Aegis.IslandPerimeter.Code.Funs

/-!
# Specifications of `Aegis.IslandPerimeter.island_perimeter`

LeetCode problem `island-perimeter`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IslandPerimeter

def nrows (grid : Slice (alloc.vec.Vec I64)) : Nat := grid.val.length

def ncols (grid : Slice (alloc.vec.Vec I64)) : Nat :=
  match grid.val with
  | [] => 0
  | row :: _ => row.val.length

def cell (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row => ((row.val[j]?).map fun x => x.val).getD 0

def cells (row col : Nat) : List (Nat × Nat) := (List.range row).product (List.range col)

def landCount (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) : Nat :=
  ((cells row col).filter fun (p : Nat × Nat) => decide (cell grid p.1 p.2 = 1)).length

def sharedSideCount (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) : Nat :=
  (((cells row col).filter fun (p : Nat × Nat) =>
        decide (cell grid p.1 p.2 = 1) && decide (p.1 + 1 < row) &&
          decide (cell grid (p.1 + 1) p.2 = 1)).length +
    ((cells row col).filter fun (p : Nat × Nat) =>
        decide (cell grid p.1 p.2 = 1) && decide (p.2 + 1 < col) &&
          decide (cell grid p.1 (p.2 + 1) = 1)).length)

inductive Dir
  | up
  | down
  | left
  | right
  deriving DecidableEq, Repr

def facesWaterB (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (i j : Nat) (d : Dir) : Bool :=
  match d with
  | Dir.up => decide (i = 0) || decide (cell grid (i - 1) j = 0)
  | Dir.down => decide (row ≤ i + 1) || decide (cell grid (i + 1) j = 0)
  | Dir.left => decide (j = 0) || decide (cell grid i (j - 1) = 0)
  | Dir.right => decide (col ≤ j + 1) || decide (cell grid i (j + 1) = 0)

def FacesWater (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (i j : Nat) (d : Dir) : Prop :=
  facesWaterB grid row col i j d = true

instance instDecidableFacesWater (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (i j : Nat)
    (d : Dir) : Decidable (FacesWater grid row col i j d) :=
  inferInstanceAs (Decidable (facesWaterB grid row col i j d = true))

def perimeter (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) : Nat :=
  (((cells row col).product [Dir.up, Dir.down, Dir.left, Dir.right]).filter
      fun (t : (Nat × Nat) × Dir) =>
        decide (cell grid t.1.1 t.1.2 = 1 ∧ FacesWater grid row col t.1.1 t.1.2 t.2)).length

def CellAdj (p q : Nat × Nat) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
    (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

def LandStep (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (p q : Nat × Nat) : Prop :=
  CellAdj p q ∧ q.1 < row ∧ q.2 < col ∧ cell grid q.1 q.2 = 1

def LandReach (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (p q : Nat × Nat) : Prop :=
  Relation.ReflTransGen (LandStep grid row col) p q

def WaterStep (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (p q : Nat × Nat) : Prop :=
  CellAdj p q ∧ q.1 < row ∧ q.2 < col ∧ cell grid q.1 q.2 = 0

def WaterReach (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) (p q : Nat × Nat) : Prop :=
  Relation.ReflTransGen (WaterStep grid row col) p q

def OnBorder (row col : Nat) (p : Nat × Nat) : Prop :=
  p.1 < row ∧ p.2 < col ∧ (p.1 = 0 ∨ p.2 = 0 ∨ p.1 + 1 = row ∨ p.2 + 1 = col)

def NoLakes (grid : Slice (alloc.vec.Vec I64)) (row col : Nat) : Prop :=
  ∀ i j, i < row → j < col → cell grid i j = 0 →
    ∃ p, OnBorder row col p ∧ WaterReach grid row col (i, j) p

/-- The function returns a result r and r is the perimeter of the island: r = B(grid), where B(grid) counts all pairs (i,j,d) such that 0 <= i < row, 0 <= j < col, grid[i][j] = 1, d is one of up, down, left, right, and the neighbor of cell (i,j) in direction d is either outside the grid or is a cell with value 0. Equivalently, r is the number of unit sides of land cells that face water or the outside.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes (no 0-cell region is completely enclosed by 1-cells away from the outside of the grid). The outside of the grid is treated as water. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∃ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r ∧
      r.val = (perimeter grid row col : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∃ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r ∧
      r.val = (perimeter grid row col : Int)) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, index out of bounds, or panic.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes. The outside of the grid is treated as water. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∃ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∃ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 4.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes. The outside of the grid is treated as water. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r → 4 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r → 4 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 4 * L, where L = |{(i,j) : 0 <= i < row and 0 <= j < col and grid[i][j] = 1}| is the number of land cells.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes. The outside of the grid is treated as water. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r →
      r.val ≤ 4 * (landCount grid row col : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r →
      r.val ≤ 4 * (landCount grid row col : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is even, that is, r mod 2 = 0.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes. The outside of the grid is treated as water. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r → r.val % 2 = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r → r.val % 2 = 0) := by
  sorry

/-- Whenever the function returns a result r, r = 4*L - 2*A, where L is the number of cells with value 1 and A is the number of unordered pairs of land cells that share a side, i.e. A = |{{{ (i,j),(i',j') } : 0 <= i,i' < row, 0 <= j,j' < col, grid[i][j] = 1, grid[i'][j'] = 1, and |i-i'| + |j-j'| = 1 }}|.
  Preconditions: grid is a rectangular 0/1 matrix: row = len(grid), col = len(grid[0]), 1 <= row <= 100, 1 <= col <= 100, every row of grid has length col, and grid[i][j] is 0 or 1 for all 0 <= i < row and 0 <= j < col. The cells with value 1 form exactly one nonempty 4-connected component using horizontal/vertical adjacency, and the island has no lakes. The outside of the grid is treated as water. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col) :
    ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r →
      r.val = 4 * (landCount grid row col : Int) - 2 * (sharedSideCount grid row col : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (row col : Nat)
    (hrows : nrows grid = row)
    (hcols : ncols grid = col)
    (hrow_pos : 1 ≤ row) (hrow_bound : row ≤ 100)
    (hcol_pos : 1 ≤ col) (hcol_bound : col ≤ 100)
    (hrow_len : ∀ (i : Nat) (r : alloc.vec.Vec I64), grid.val[i]? = some r → r.val.length = col)
    (hbin : ∀ i j, i < row → j < col → cell grid i j = 0 ∨ cell grid i j = 1)
    (hisland_ne : ∃ i j, i < row ∧ j < col ∧ cell grid i j = 1)
    (hisland_conn : ∀ i j i' j', i < row → j < col → i' < row → j' < col →
      cell grid i j = 1 → cell grid i' j' = 1 →
      LandReach grid row col (i, j) (i', j'))
    (hnolakes : NoLakes grid row col), ∀ (r : I64), Aegis.IslandPerimeter.island_perimeter grid = ok r →
      r.val = 4 * (landCount grid row col : Int) - 2 * (sharedSideCount grid row col : Int)) := by
  sorry

end AegisSpec.IslandPerimeter
