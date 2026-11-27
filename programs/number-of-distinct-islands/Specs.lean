import Aegis.NumDistinctIslands.Code.Funs

/-!
# Specifications of `Aegis.NumDistinctIslands.num_distinct_islands`

LeetCode problem `number-of-distinct-islands`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumDistinctIslands

abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

def gridM (grid : Grid) : Nat := grid.val.length

def gridN (grid : Grid) : Nat :=
  match grid.val with
  | [] => 0
  | row :: _ => row.val.length

def RowsLength (grid : Grid) : Prop := ∀ row ∈ grid.val, row.val.length = gridN grid

def cell (grid : Grid) (i j : Nat) : Option Int :=
  match grid.val[i]? with
  | none => none
  | some row => (row.val[j]?).map (fun x => x.val)

def GridPre (grid : Grid) : Prop :=
  1 ≤ gridM grid ∧ gridM grid ≤ 50 ∧ 1 ≤ gridN grid ∧ gridN grid ≤ 50 ∧
  RowsLength grid ∧
  (∀ i j, i < gridM grid → j < gridN grid →
    cell grid i j = some 0 ∨ cell grid i j = some 1)

def Land (grid : Grid) (p : Nat × Nat) : Prop := cell grid p.1 p.2 = some 1

def Adj (p q : Nat × Nat) : Prop :=
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1)) ∨
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2))

def LandReach (grid : Grid) (p q : Nat × Nat) : Prop :=
  Relation.ReflTransGen (fun a b => Land grid a ∧ Land grid b ∧ Adj a b) p q

def IsIsland (grid : Grid) (S : Finset (Nat × Nat)) : Prop :=
  S.Nonempty ∧ (∀ p ∈ S, Land grid p) ∧
  (∀ p ∈ S, ∀ q ∈ S, LandReach grid p q) ∧
  (∀ p, Land grid p → (∃ q ∈ S, LandReach grid p q) → p ∈ S)

def gridCells (grid : Grid) : Finset (Nat × Nat) :=
  Finset.range (gridM grid) ×ˢ Finset.range (gridN grid)

noncomputable def islandsOf (grid : Grid) : Finset (Finset (Nat × Nat)) := by
  classical
  exact (gridCells grid).powerset.filter (fun S => IsIsland grid S)

noncomputable def minRow (S : Finset (Nat × Nat)) (h : S.Nonempty) : Nat :=
  S.inf' h (fun p => p.1)

noncomputable def minCol (S : Finset (Nat × Nat)) (h : S.Nonempty) : Nat :=
  S.inf' h (fun p => p.2)

noncomputable def normShape (S : Finset (Nat × Nat)) (h : S.Nonempty) :
    Finset (Nat × Nat) :=
  S.image (fun p => (p.1 - minRow S h, p.2 - minCol S h))

noncomputable def shapeOf (S : Finset (Nat × Nat)) : Finset (Nat × Nat) := by
  classical
  exact if h : S.Nonempty then normShape S h else ∅

def TranslationEq (S T : Finset (Nat × Nat)) : Prop :=
  ∃ dr dc : Int, ∀ p, p ∈ T ↔
    ∃ q ∈ S, (q.1 : Int) + dr = (p.1 : Int) ∧ (q.2 : Int) + dc = (p.2 : Int)

noncomputable def numShapes (grid : Grid) : Nat :=
  ((islandsOf grid).image shapeOf).card

noncomputable def islandSizes (grid : Grid) : Finset Nat :=
  (islandsOf grid).image (fun S => S.card)

def RowRun (grid : Grid) (a b : Nat) : Prop :=
  a ≤ b ∧ b < gridN grid ∧
  (∀ j, a ≤ j → j ≤ b → cell grid 0 j = some 1) ∧
  (a = 0 ∨ cell grid 0 (a - 1) = some 0) ∧
  (b = gridN grid - 1 ∨ cell grid 0 (b + 1) = some 0)

noncomputable def rowRuns (grid : Grid) : Finset (Nat × Nat) := by
  classical
  exact (Finset.range (gridN grid) ×ˢ Finset.range (gridN grid)).filter
    (fun p => RowRun grid p.1 p.2)

noncomputable def rowRunLengths (grid : Grid) : Finset Nat :=
  (rowRuns grid).image (fun p => p.2 - p.1 + 1)

def ColRun (grid : Grid) (a b : Nat) : Prop :=
  a ≤ b ∧ b < gridM grid ∧
  (∀ i, a ≤ i → i ≤ b → cell grid i 0 = some 1) ∧
  (a = 0 ∨ cell grid (a - 1) 0 = some 0) ∧
  (b = gridM grid - 1 ∨ cell grid (b + 1) 0 = some 0)

noncomputable def colRuns (grid : Grid) : Finset (Nat × Nat) := by
  classical
  exact (Finset.range (gridM grid) ×ˢ Finset.range (gridM grid)).filter
    (fun p => ColRun grid p.1 p.2)

noncomputable def colRunLengths (grid : Grid) : Finset Nat :=
  (colRuns grid).image (fun p => p.2 - p.1 + 1)

def IsHReflect (grid gridR : Grid) : Prop :=
  gridM gridR = gridM grid ∧ gridN gridR = gridN grid ∧ RowsLength gridR ∧
  ∀ i j, i < gridM grid → j < gridN grid →
    cell gridR i j = cell grid i (gridN grid - 1 - j)

def IsVReflect (grid gridV : Grid) : Prop :=
  gridM gridV = gridM grid ∧ gridN gridV = gridN grid ∧ RowsLength gridV ∧
  ∀ i j, i < gridM grid → j < gridN grid →
    cell gridV i j = cell grid (gridM grid - 1 - i) j

def IsTranspose (grid gridT : Grid) : Prop :=
  gridM gridT = gridN grid ∧ gridN gridT = gridM grid ∧ RowsLength gridT ∧
  ∀ i j, i < gridN grid → j < gridM grid → cell gridT i j = cell grid j i

/-- Whenever num_distinct_islands returns a result r, r is the number of distinct island shapes up to translation. Precisely: call a cell (i,j) land if grid[i][j]=1; an island is a maximal nonempty set S of land cells such that any two cells of S are connected by a path of cells in S whose successive cells differ by 1 in exactly one coordinate and by 0 in the other (4-directional adjacency). Two islands S,T are equivalent iff there exist integers dr,dc with T = {(i+dr, j+dc) : (i,j) in S}. Then r equals the number of equivalence classes of all islands of grid under this relation.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (grid : Grid) (hpre : GridPre grid) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = (numShapes grid : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = (numShapes grid : Int)) := by
  sorry

/-- For every grid satisfying the preconditions, num_distinct_islands returns a result r; in particular it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (grid : Grid) (hpre : GridPre grid) :
    ∃ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∃ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r) := by
  sorry

/-- Whenever num_distinct_islands returns a result r, r <= C, where C is the number of islands of grid, i.e. the number of maximal 4-connected components of cells with value 1. Consequently r <= m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (grid : Grid) (hpre : GridPre grid) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val ≤ ((islandsOf grid).card : Int) ∧
      r.val ≤ ((gridM grid) * (gridN grid) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val ≤ ((islandsOf grid).card : Int) ∧
      r.val ≤ ((gridM grid) * (gridN grid) : Int)) := by
  sorry

/-- Whenever num_distinct_islands returns a result r, r = 0 if and only if grid[i][j]=0 for every 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (grid : Grid) (hpre : GridPre grid) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      (r.val = 0 ↔ ∀ i, i < gridM grid → ∀ j, j < gridN grid →
        cell grid i j = some 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      (r.val = 0 ↔ ∀ i, i < gridM grid → ∀ j, j < gridN grid →
        cell grid i j = some 0)) := by
  sorry

/-- Whenever num_distinct_islands returns a result r, r = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Assume grid has exactly one island, i.e. exactly one maximal 4-connected component of cells with value 1. -/
theorem spec_5 (grid : Grid) (hpre : GridPre grid)
    (hislands : (islandsOf grid).card = 1) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r → r.val = 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid)
    (hislands : (islandsOf grid).card = 1), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r → r.val = 1) := by
  sorry

/-- For the single row, call a run a maximal nonempty interval [a,b] of columns such that grid[0][j]=1 for every a <= j <= b, and either a=0 or grid[0][a-1]=0, and either b=n-1 or grid[0][b+1]=0. Let D be the set of lengths b-a+1 of all such runs. Whenever num_distinct_islands returns a result r, r equals the number of elements of D.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Assume m = 1. -/
theorem spec_6 (grid : Grid) (hpre : GridPre grid) (hm : gridM grid = 1) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = ((rowRunLengths grid).card : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (hm : gridM grid = 1), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = ((rowRunLengths grid).card : Int)) := by
  sorry

/-- For the single column, call a run a maximal nonempty interval [a,b] of rows such that grid[i][0]=1 for every a <= i <= b, and either a=0 or grid[a-1][0]=0, and either b=m-1 or grid[b+1][0]=0. Let D be the set of lengths b-a+1 of all such runs. Whenever num_distinct_islands returns a result r, r equals the number of elements of D.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Assume n = 1. -/
theorem spec_7 (grid : Grid) (hpre : GridPre grid) (hn : gridN grid = 1) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = ((colRunLengths grid).card : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (hn : gridN grid = 1), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      r.val = ((colRunLengths grid).card : Int)) := by
  sorry

/-- Whenever num_distinct_islands(grid) returns r and num_distinct_islands(grid') returns r', we have r = r'.
  Preconditions: Let grid satisfy the base preconditions: m = len(grid), n = len(grid[0]), every row has length n, 1 <= m,n <= 50, and all entries are in {0,1}. Let grid' be any valid grid with m' rows and n' columns (all entries in {0,1}) for which there exist integers top,bottom,left,right >= 0 such that m'=m+top+bottom, n'=n+left+right, grid'[i+top][j+left]=grid[i][j] for all 0 <= i < m and 0 <= j < n, and grid'[u][v]=0 for every other cell (u,v) of grid'. -/
theorem spec_8 (grid grid' : Grid) (hpre : GridPre grid) (hpre' : GridPre grid')
    (top bottom left right : Nat)
    (hm' : gridM grid' = gridM grid + top + bottom)
    (hn' : gridN grid' = gridN grid + left + right)
    (hinner : ∀ i j, i < gridM grid → j < gridN grid →
      cell grid' (i + top) (j + left) = cell grid i j)
    (houter : ∀ u v, u < gridM grid' → v < gridN grid' →
      (u < top ∨ top + gridM grid ≤ u ∨ v < left ∨ left + gridN grid ≤ v) →
      cell grid' u v = some 0) :
    ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands grid' = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid grid' : Grid) (hpre : GridPre grid) (hpre' : GridPre grid')
    (top bottom left right : Nat)
    (hm' : gridM grid' = gridM grid + top + bottom)
    (hn' : gridN grid' = gridN grid + left + right)
    (hinner : ∀ i j, i < gridM grid → j < gridN grid →
      cell grid' (i + top) (j + left) = cell grid i j)
    (houter : ∀ u v, u < gridM grid' → v < gridN grid' →
      (u < top ∨ top + gridM grid ≤ u ∨ v < left ∨ left + gridN grid ≤ v) →
      cell grid' u v = some 0), ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands grid' = ok r' → r = r') := by
  sorry

/-- Whenever num_distinct_islands returns a result r, r is at least the number of distinct positive integers that occur as the size |S| (number of cells) of an island S of grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. -/
theorem spec_9 (grid : Grid) (hpre : GridPre grid) :
    ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      (((islandSizes grid).filter (fun k => 0 < k)).card : Int) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∀ r, Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      (((islandSizes grid).filter (fun k => 0 < k)).card : Int) ≤ r.val) := by
  sorry

/-- Whenever num_distinct_islands(grid) returns r and num_distinct_islands(grid^R) returns r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Let grid^R be the horizontal reflection of grid, with the same m and n and grid^R[i][j] = grid[i][n-1-j] for all 0 <= i < m and 0 <= j < n. -/
theorem spec_10 (grid gridR : Grid) (hpre : GridPre grid) (hR : IsHReflect grid gridR) :
    ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridR = ok r' → r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Grid) (hpre : GridPre grid) (hR : IsHReflect grid gridR), ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridR = ok r' → r = r') := by
  sorry

/-- Whenever num_distinct_islands(grid) returns r and num_distinct_islands(grid^V) returns r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Let grid^V be the vertical reflection of grid, with the same m and n and grid^V[i][j] = grid[m-1-i][j] for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (grid gridV : Grid) (hpre : GridPre grid) (hV : IsVReflect grid gridV) :
    ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridV = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid gridV : Grid) (hpre : GridPre grid) (hV : IsVReflect grid gridV), ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridV = ok r' → r = r') := by
  sorry

/-- Whenever num_distinct_islands(grid) returns r and num_distinct_islands(grid^T) returns r', we have r = r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]), with every row of grid having length n. Assume 1 <= m,n <= 50 and grid[i][j] in {0,1} for every 0 <= i < m and 0 <= j < n. Let grid^T be the transpose of grid, with n rows and m columns and grid^T[i][j] = grid[j][i] for all 0 <= i < n and 0 <= j < m. -/
theorem spec_12 (grid gridT : Grid) (hpre : GridPre grid) (hT : IsTranspose grid gridT) :
    ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridT = ok r' → r = r' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid gridT : Grid) (hpre : GridPre grid) (hT : IsTranspose grid gridT), ∀ r r', Aegis.NumDistinctIslands.num_distinct_islands grid = ok r →
      Aegis.NumDistinctIslands.num_distinct_islands gridT = ok r' → r = r') := by
  sorry

end AegisSpec.NumDistinctIslands
