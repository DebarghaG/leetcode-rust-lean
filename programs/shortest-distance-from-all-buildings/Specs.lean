import Aegis.ShortestDistance.Code.Funs

/-!
# Specifications of `Aegis.ShortestDistance.shortest_distance`

LeetCode problem `shortest-distance-from-all-buildings`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.ShortestDistance

def gridRows (grid : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def m (grid : Slice (alloc.vec.Vec I64)) : Nat :=
  (gridRows grid).length

def n (grid : Slice (alloc.vec.Vec I64)) : Nat :=
  match gridRows grid with
  | [] => 0
  | row :: _ => row.length

def rowLen (grid : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat :=
  (((gridRows grid)[i]?).map List.length).getD 0

def cellVal (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  (((gridRows grid)[i]?).bind (fun row => row[j]?)).getD 0

def InGrid (grid : Slice (alloc.vec.Vec I64)) (p : Nat × Nat) : Prop :=
  p.1 < m grid ∧ p.2 < n grid

def IsEmpty (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
  cellVal grid i j = 0

def IsBuilding (grid : Slice (alloc.vec.Vec I64)) (i j : Nat) : Prop :=
  cellVal grid i j = 1

def Adjacent (p q : Nat × Nat) : Prop :=
  (p.1 + 1 = q.1 ∧ p.2 = q.2) ∨ (q.1 + 1 = p.1 ∧ p.2 = q.2) ∨
    (p.1 = q.1 ∧ p.2 + 1 = q.2) ∨ (p.1 = q.1 ∧ q.2 + 1 = p.2)

def ChainAdj : List (Nat × Nat) → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => Adjacent a b ∧ ChainAdj (b :: t)

def LegalPath (grid : Slice (alloc.vec.Vec I64)) (p q : Nat × Nat) (k : Nat) : Prop :=
  ∃ l : List (Nat × Nat),
    l.length = k + 1 ∧ ChainAdj l ∧ l.head? = some p ∧ l.getLast? = some q ∧
      (∀ c, c ∈ l → InGrid grid c) ∧
      (∀ i, i < k → ∀ c, l[i]? = some c → IsEmpty grid c.1 c.2)

noncomputable def distGrid (grid : Slice (alloc.vec.Vec I64)) (p q : Nat × Nat) : Option Nat :=
  if h : ∃ k, 1 ≤ k ∧ LegalPath grid p q k then some (Nat.find h) else none

def IsValidHouse (grid : Slice (alloc.vec.Vec I64)) (p : Nat × Nat) : Prop :=
  InGrid grid p ∧ IsEmpty grid p.1 p.2 ∧
    ∀ i j, i < m grid → j < n grid → IsBuilding grid i j →
      distGrid grid p (i, j) ≠ none

noncomputable def totalDistance (grid : Slice (alloc.vec.Vec I64)) (p : Nat × Nat) : Nat :=
  ∑ i ∈ Finset.range (m grid), ∑ j ∈ Finset.range (n grid),
    if IsBuilding grid i j then (distGrid grid p (i, j)).getD 0 else 0

noncomputable def buildingCount (grid : Slice (alloc.vec.Vec I64)) : Nat :=
  ∑ i ∈ Finset.range (m grid), ∑ j ∈ Finset.range (n grid),
    if IsBuilding grid i j then 1 else 0

def IsMinTotal (grid : Slice (alloc.vec.Vec I64)) (r : Int) : Prop :=
  (∃ p, IsValidHouse grid p ∧ (totalDistance grid p : Int) = r) ∧
    ∀ p, IsValidHouse grid p → r ≤ (totalDistance grid p : Int)

noncomputable def SpecResult (grid : Slice (alloc.vec.Vec I64)) (r : Int) : Prop :=
  if ∃ p, IsValidHouse grid p then IsMinTotal grid r else r = -1

/-- Whenever shortest_distance(grid) returns a result r, r is characterized as follows. For an empty cell p=(i,j) with grid[i][j]=0 and a building cell q, let dist_grid(p,q) be the least k >= 1 such that there is a sequence p=p_0,p_1,...,p_k=q of cells where each consecutive pair is side-adjacent (differs by 1 in exactly one coordinate) and p_0,...,p_{k-1} all have grid value 0; if no such k exists, dist_grid(p,q) is undefined. Call an empty cell p a valid house if dist_grid(p,q) is defined for every building q. For a valid house p, define total_distance(p) = sum over all building cells q of dist_grid(p,q). Then r is the minimum of total_distance(p) over all valid houses p, if at least one valid house exists; otherwise r = -1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r) :
    SpecResult grid r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r), SpecResult grid r.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access outside the grid for any input satisfying the preconditions.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j) :
    ∃ r, Aegis.ShortestDistance.shortest_distance grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j), ∃ r, Aegis.ShortestDistance.shortest_distance grid = ok r) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r with r != -1, we have r >= B, where B is the number of cells with value 1 in grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1) :
    (buildingCount grid : Int) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1), (buildingCount grid : Int) ≤ r.val) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r with r != -1, we have r <= B * (m * n - 1), where B is the number of cells with value 1 in grid.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1) :
    r.val ≤ (buildingCount grid : Int) * ((m grid : Int) * (n grid : Int) - 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1), r.val ≤ (buildingCount grid : Int) * ((m grid : Int) * (n grid : Int) - 1)) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r with r != -1, there exists a cell p=(i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j]=0 such that for every building cell q, the shortest legal side-adjacent path from p to q whose cells before q are all empty exists, and r is the sum of those path lengths over all building cells q.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1) :
    ∃ p, IsValidHouse grid p ∧ r.val = (totalDistance grid p : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1), ∃ p, IsValidHouse grid p ∧ r.val = (totalDistance grid p : Int)) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r with r != -1, for every empty cell p=(i,j) with 0 <= i < m, 0 <= j < n, and grid[i][j]=0 such that for every building cell q there exists a legal side-adjacent path from p to q whose cells before q are all empty, let dist_grid(p,q) be the least k >= 1 for which there is a sequence p=p_0,...,p_k=q of grid cells with each consecutive pair side-adjacent and p_0,...,p_{k-1} all having grid value 0. Then the sum over all building cells q of dist_grid(p,q) is at least r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1) :
    ∀ p, IsValidHouse grid p → r.val ≤ (totalDistance grid p : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hne : r.val ≠ -1), ∀ p, IsValidHouse grid p → r.val ≤ (totalDistance grid p : Int)) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r, r = -1 if and only if there is no empty cell p=(i,j) from which every building cell q is reachable by a legal side-adjacent path whose cells before q are all empty.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r) :
    (r.val = -1 ↔ ¬ ∃ p, IsValidHouse grid p) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r), (r.val = -1 ↔ ¬ ∃ p, IsValidHouse grid p)) := by
  sorry

/-- Whenever shortest_distance(grid) returns a result r, r = 1.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; there is exactly one cell b=(r,c) with grid[r][c] = 1; and there exists an empty cell side-adjacent to b (a cell differing from b by 1 in exactly one coordinate). -/
theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (b : Nat × Nat) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hb : b.1 < m grid ∧ b.2 < n grid ∧ IsBuilding grid b.1 b.2)
    (huniq : ∀ p, p.1 < m grid → p.2 < n grid → IsBuilding grid p.1 p.2 → p = b)
    (hadj : ∃ i j, i < m grid ∧ j < n grid ∧ IsEmpty grid i j ∧ Adjacent (i, j) b)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r) :
    r.val = 1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (b : Nat × Nat) (r : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hb : b.1 < m grid ∧ b.2 < n grid ∧ IsBuilding grid b.1 b.2)
    (huniq : ∀ p, p.1 < m grid → p.2 < n grid → IsBuilding grid p.1 p.2 → p = b)
    (hadj : ∃ i j, i < m grid ∧ j < n grid ∧ IsEmpty grid i j ∧ Adjacent (i, j) b)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r), r.val = 1) := by
  sorry

/-- Let gridT be the n by m grid defined by gridT[j][i] = grid[i][j]. Whenever shortest_distance(grid) returns r and shortest_distance(gridT) returns rT, we have r = rT.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_9 (grid gridT : Slice (alloc.vec.Vec I64)) (r rT : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hTm : m gridT = n grid) (hTn : n gridT = m grid)
    (hT : ∀ i j, i < m grid → j < n grid → cellVal gridT j i = cellVal grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hresT : Aegis.ShortestDistance.shortest_distance gridT = ok rT) :
    r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (r rT : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hTm : m gridT = n grid) (hTn : n gridT = m grid)
    (hT : ∀ i j, i < m grid → j < n grid → cellVal gridT j i = cellVal grid i j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hresT : Aegis.ShortestDistance.shortest_distance gridT = ok rT), r.val = rT.val) := by
  sorry

/-- Let gridR be the m by n grid defined by gridR[i][j] = grid[m-1-i][j]. Whenever shortest_distance(grid) returns r and shortest_distance(gridR) returns rR, we have r = rR.
  Preconditions: Let m = len(grid) and n = len(grid[0]). We assume 1 <= m,n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, grid[i][j] is 0, 1, or 2; and there is at least one cell (i,j) with grid[i][j] = 1. -/
theorem spec_10 (grid gridR : Slice (alloc.vec.Vec I64)) (r rR : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hRm : m gridR = m grid) (hRn : n gridR = n grid)
    (hR : ∀ i j, i < m grid → j < n grid →
      cellVal gridR i j = cellVal grid (m grid - 1 - i) j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hresR : Aegis.ShortestDistance.shortest_distance gridR = ok rR) :
    r.val = rR.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid gridR : Slice (alloc.vec.Vec I64)) (r rR : I64)
    (hm : 1 ≤ m grid) (hm50 : m grid ≤ 50) (hn : 1 ≤ n grid) (hn50 : n grid ≤ 50)
    (hrows : ∀ i, i < m grid → rowLen grid i = n grid)
    (hvals : ∀ i j, i < m grid → j < n grid →
      cellVal grid i j = 0 ∨ cellVal grid i j = 1 ∨ cellVal grid i j = 2)
    (hbuild : ∃ i j, i < m grid ∧ j < n grid ∧ IsBuilding grid i j)
    (hRm : m gridR = m grid) (hRn : n gridR = n grid)
    (hR : ∀ i j, i < m grid → j < n grid →
      cellVal gridR i j = cellVal grid (m grid - 1 - i) j)
    (hres : Aegis.ShortestDistance.shortest_distance grid = ok r)
    (hresR : Aegis.ShortestDistance.shortest_distance gridR = ok rR), r.val = rR.val) := by
  sorry

end AegisSpec.ShortestDistance
