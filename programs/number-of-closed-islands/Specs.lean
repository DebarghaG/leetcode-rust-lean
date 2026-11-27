import Aegis.ClosedIsland.Code.Funs

/-!
# Specifications of `Aegis.ClosedIsland.closed_island`

LeetCode problem `number-of-closed-islands`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.ClosedIsland

abbrev Grid : Type := Slice (alloc.vec.Vec I64)

def toLists (grid : Grid) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def numRowsOf (a : List (List Int)) : Nat := a.length

def numColsOf (a : List (List Int)) : Nat := (a.headD []).length

def cell (a : List (List Int)) (i j : Nat) : Option Int := (a[i]?).bind (fun row => row[j]?)

def numRows (grid : Grid) : Nat := numRowsOf (toLists grid)

def numCols (grid : Grid) : Nat := numColsOf (toLists grid)

def rowLenAt (grid : Grid) (i : Nat) : Option Nat :=
  (grid.val[i]?).map (fun row => row.val.length)

def InBounds (a : List (List Int)) (p : Nat × Nat) : Prop :=
  p.1 < numRowsOf a ∧ p.2 < numColsOf a

def IsLand (a : List (List Int)) (p : Nat × Nat) : Prop := cell a p.1 p.2 = some 0

def IsWater (a : List (List Int)) (p : Nat × Nat) : Prop := cell a p.1 p.2 = some 1

def Adj (p q : Nat × Nat) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨ (p.1 = q.1 ∧ q.2 + 1 = p.2)

def AdjIn (S : Set (Nat × Nat)) (p q : Nat × Nat) : Prop := p ∈ S ∧ q ∈ S ∧ Adj p q

def Connected (S : Set (Nat × Nat)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen (AdjIn S) p q

def LandCells (a : List (List Int)) : Set (Nat × Nat) := {p | IsLand a p}

def IsLandIsland (a : List (List Int)) (S : Set (Nat × Nat)) : Prop :=
  S.Nonempty ∧ Connected S ∧ (∀ p ∈ S, IsLand a p) ∧
    (∀ p ∈ S, ∀ q, IsLand a q → Adj p q → q ∈ S)

def landIslands (a : List (List Int)) : Set (Set (Nat × Nat)) := {S | IsLandIsland a S}

noncomputable def landIslandCount (a : List (List Int)) : Nat := (landIslands a).ncard

def IsInterior (a : List (List Int)) (p : Nat × Nat) : Prop :=
  1 ≤ p.1 ∧ p.1 + 2 ≤ numRowsOf a ∧ 1 ≤ p.2 ∧ p.2 + 2 ≤ numColsOf a

def IsBoundaryCell (a : List (List Int)) (p : Nat × Nat) : Prop :=
  InBounds a p ∧ (p.1 = 0 ∨ p.1 + 1 = numRowsOf a ∨ p.2 = 0 ∨ p.2 + 1 = numColsOf a)

def IsClosedIsland (a : List (List Int)) (S : Set (Nat × Nat)) : Prop :=
  IsLandIsland a S ∧ ∀ p ∈ S, IsInterior a p

def closedIslands (a : List (List Int)) : Set (Set (Nat × Nat)) := {S | IsClosedIsland a S}

noncomputable def closedIslandCount (a : List (List Int)) : Nat := (closedIslands a).ncard

def islandUpperBound (a : List (List Int)) : Nat :=
  if numRowsOf a < 2 ∨ numColsOf a < 2 then 0 else (numRowsOf a - 2) * (numColsOf a - 2)

def AllWater (a : List (List Int)) : Prop := ∀ p, InBounds a p → IsWater a p

def AllLand (a : List (List Int)) : Prop := ∀ p, InBounds a p → IsLand a p

def BoundaryAllWater (a : List (List Int)) : Prop := ∀ p, IsBoundaryCell a p → IsWater a p

def ReachesBoundary (a : List (List Int)) (p : Nat × Nat) : Prop :=
  IsLand a p ∧ ∃ q, IsLand a q ∧ IsBoundaryCell a q ∧
    Relation.ReflTransGen (AdjIn (LandCells a)) p q

def UniqueLandCell (a : List (List Int)) (p : Nat × Nat) : Prop :=
  IsLand a p ∧ ∀ q, IsLand a q → q = p

def transpose (a : List (List Int)) : List (List Int) :=
  (List.range (numColsOf a)).map
    (fun j => (List.range (numRowsOf a)).map (fun i => (cell a i j).getD 0))

def rotate180 (a : List (List Int)) : List (List Int) := (a.map List.reverse).reverse

def AllBinary (a : List (List Int)) : Prop :=
  ∀ p, InBounds a p → cell a p.1 p.2 = some 0 ∨ cell a p.1 p.2 = some 1

def GridPre (grid : Grid) : Prop :=
  1 ≤ numRows grid ∧ numRows grid ≤ 100 ∧
    1 ≤ numCols grid ∧ numCols grid ≤ 100 ∧
      (∀ i, i < numRows grid → rowLenAt grid i = some (numCols grid)) ∧
        AllBinary (toLists grid)

/-- Whenever the function returns a result r, r equals the number of closed islands of grid, defined as follows. A cell is a pair (i,j) with 0 <= i < R and 0 <= j < C; it is land if grid[i][j] = 0 and water if grid[i][j] = 1. Two cells (i,j) and (i',j') are 4-adjacent if |i-i'| + |j-j'| = 1. A set S of cells is 4-connected if for every a,b in S there is a finite sequence a = c_0, c_1, ..., c_k = b of cells in S such that c_t and c_{t+1} are 4-adjacent for every 0 <= t < k (and k = 0 when a = b). A land island is a maximal 4-connected set of land cells: S is a land island if S is a nonempty 4-connected set of land cells and no land cell outside S is 4-adjacent to any cell in S. A cell (i,j) is interior if 1 <= i <= R-2 and 1 <= j <= C-2; otherwise it lies on the grid boundary (i=0 or i=R-1 or j=0 or j=C-1). A land island is closed if every cell in it is interior. Then r is the number of closed islands.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_1 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val = (closedIslandCount (toLists grid) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val = (closedIslandCount (toLists grid) : Int)) := by
  sorry

/-- The function returns a result r of type i64; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_2 (grid : Grid) (hpre : GridPre grid) :
    ∃ r : I64, Aegis.ClosedIsland.closed_island grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid), ∃ r : I64, Aegis.ClosedIsland.closed_island grid = ok r) := by
  sorry

/-- Whenever the function returns r, 0 <= r.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_3 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), 0 ≤ r.val) := by
  sorry

/-- Whenever the function returns r, r <= I, where I is defined by I = 0 if R < 2 or C < 2, and I = (R-2)*(C-2) otherwise.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_4 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val ≤ (islandUpperBound (toLists grid) : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val ≤ (islandUpperBound (toLists grid) : Int)) := by
  sorry

/-- Whenever the function returns r, if R <= 2 or C <= 2 then r = 0.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_5 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r)
    (hsmall : numRows grid ≤ 2 ∨ numCols grid ≤ 2) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r)
    (hsmall : numRows grid ≤ 2 ∨ numCols grid ≤ 2), r.val = 0) := by
  sorry

/-- Whenever the function returns r, if grid[i][j] = 1 for every valid cell (i,j), then r = 0.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_6 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) (hall : AllWater (toLists grid)) :
    r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) (hall : AllWater (toLists grid)), r.val = 0) := by
  sorry

/-- Whenever the function returns r, if grid[i][j] = 0 for every valid cell (i,j), then r = 0.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_7 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) (hall : AllLand (toLists grid)) :
    r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) (hall : AllLand (toLists grid)), r.val = 0) := by
  sorry

/-- Whenever the function returns r, if grid[i][j] = 1 for every boundary cell (every (i,j) with 0 <= i < R, 0 <= j < C, and (i=0 or i=R-1 or j=0 or j=C-1)), then r equals the total number of land islands of grid, where a land island is a maximal 4-connected set of land cells as defined in spec_1 without the closedness condition.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_8 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r)
    (hbdy : BoundaryAllWater (toLists grid)) :
    r.val = (landIslandCount (toLists grid) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r)
    (hbdy : BoundaryAllWater (toLists grid)), r.val = (landIslandCount (toLists grid) : Int)) := by
  sorry

/-- Whenever the function returns r, r = 0 if and only if every land cell is connected to some boundary cell by a path of land cells; that is, for every land cell (i,j) there exists a sequence (i_0,j_0), ..., (i_k,j_k) of land cells with (i_0,j_0)=(i,j), each consecutive pair 4-adjacent, and the last cell (i_k,j_k) satisfying i_k=0 or i_k=R-1 or j_k=0 or j_k=C-1.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_9 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    (r.val = 0 ↔ ∀ p, IsLand (toLists grid) p → ReachesBoundary (toLists grid) p) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), (r.val = 0 ↔ ∀ p, IsLand (toLists grid) p → ReachesBoundary (toLists grid) p)) := by
  sorry

/-- Whenever the function returns r, if there is exactly one cell (i0,j0) with grid[i0][j0] = 0, and 1 <= i0 <= R-2 and 1 <= j0 <= C-2, then r = 1.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_10 (grid : Grid) (hpre : GridPre grid) (i0 j0 : Nat)
    (hunique : UniqueLandCell (toLists grid) (i0, j0))
    (hint : IsInterior (toLists grid) (i0, j0)) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (i0 j0 : Nat)
    (hunique : UniqueLandCell (toLists grid) (i0, j0))
    (hint : IsInterior (toLists grid) (i0, j0)) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val = 1) := by
  sorry

/-- Whenever the function returns r, if there is exactly one cell (i0,j0) with grid[i0][j0] = 0, and (i0=0 or i0=R-1 or j0=0 or j0=C-1), then r = 0.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_11 (grid : Grid) (hpre : GridPre grid) (i0 j0 : Nat)
    (hunique : UniqueLandCell (toLists grid) (i0, j0))
    (hbdy : IsBoundaryCell (toLists grid) (i0, j0)) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val = 0 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (i0 j0 : Nat)
    (hunique : UniqueLandCell (toLists grid) (i0, j0))
    (hbdy : IsBoundaryCell (toLists grid) (i0, j0)) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val = 0) := by
  sorry

/-- Let grid^T be the C-row, R-column grid defined by len(grid^T) = C, len(grid^T[j]) = R for every 0 <= j < C, and grid^T[j][i] = grid[i][j] for every 0 <= i < R and 0 <= j < C. Whenever the function returns r on grid, r equals the number of closed islands of grid^T, where closed islands of grid^T are defined by the same definition as in spec_1 with grid^T in place of grid.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_12 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val = (closedIslandCount (transpose (toLists grid)) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val = (closedIslandCount (transpose (toLists grid)) : Int)) := by
  sorry

/-- Let grid^R be the R-row, C-column grid defined by grid^R[i][j] = grid[R-1-i][C-1-j] for every 0 <= i < R and 0 <= j < C. Whenever the function returns r on grid, r equals the number of closed islands of grid^R, where closed islands of grid^R are defined by the same definition as in spec_1 with grid^R in place of grid.
  Preconditions: Let R = len(grid) and C = len(grid[0]). Assume 1 <= R <= 100, 1 <= C <= 100, len(grid[i]) = C for every 0 <= i < R, and grid[i][j] ∈ {0,1} for every 0 <= i < R and 0 <= j < C. -/
theorem spec_13 (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r) :
    r.val = (closedIslandCount (rotate180 (toLists grid)) : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Grid) (hpre : GridPre grid) (r : I64)
    (hres : Aegis.ClosedIsland.closed_island grid = ok r), r.val = (closedIslandCount (rotate180 (toLists grid)) : Int)) := by
  sorry

end AegisSpec.ClosedIsland
