import Aegis.NumDistinctIslands2.Code.Funs

/-!
# Specifications of `Aegis.NumDistinctIslands2.num_distinct_islands2`

LeetCode problem `number-of-distinct-islands-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumDistinctIslands2

def gridContents (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.val.map (fun row => row.val.map (fun x => x.val))

def rowAt (G : List (List Int)) (i : ℕ) : List Int := G.getD i []

def cellAt (G : List (List Int)) (i j : ℕ) : Int := (rowAt G i).getD j 0

def IsBitGrid (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
  grid.val.length = m ∧ 1 ≤ m ∧ m ≤ 50 ∧ 1 ≤ n ∧ n ≤ 50 ∧
    (∀ row ∈ grid.val, row.val.length = n) ∧
    (∀ row ∈ grid.val, ∀ x ∈ row.val, x.val = 0 ∨ x.val = 1)

abbrev Cell := ℤ × ℤ

def Adj4 (p q : Cell) : Prop :=
  (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1

def land (G : List (List Int)) (p : Cell) : Prop :=
  0 ≤ p.1 ∧ p.1 < (G.length : ℤ) ∧ 0 ≤ p.2 ∧
    p.2 < ((rowAt G p.1.toNat).length : ℤ) ∧ cellAt G p.1.toNat p.2.toNat = 1

def IsIsland (G : List (List Int)) (S : Set Cell) : Prop :=
  S.Nonempty ∧
    (∀ p, p ∈ S → land G p) ∧
    (∀ p ∈ S, ∀ q ∈ S, Relation.ReflTransGen Adj4 p q) ∧
    (∀ p ∈ S, ∀ q, land G q → Relation.ReflTransGen Adj4 p q → q ∈ S)

noncomputable def numIslands (G : List (List Int)) : ℕ :=
  Nat.card { S : Set Cell // IsIsland G S }

noncomputable def numLand (G : List (List Int)) : ℕ :=
  Nat.card { p : Cell // land G p }

inductive Sym8 where
  | id : Sym8
  | rot90 : Sym8
  | rot180 : Sym8
  | rot270 : Sym8
  | reflVert : Sym8
  | reflHoriz : Sym8
  | reflDiag : Sym8
  | reflAntiDiag : Sym8
  deriving DecidableEq, Repr

def Sym8.apply : Sym8 → Cell → Cell
  | .id, p => (p.1, p.2)
  | .rot90, p => (-p.2, p.1)
  | .rot180, p => (-p.1, -p.2)
  | .rot270, p => (p.2, -p.1)
  | .reflVert, p => (-p.1, p.2)
  | .reflHoriz, p => (p.1, -p.2)
  | .reflDiag, p => (p.2, p.1)
  | .reflAntiDiag, p => (-p.2, -p.1)

def IslandEquiv (S T : Set Cell) : Prop :=
  ∃ t : Sym8, ∃ a b : ℤ,
    T = (fun p => (a + (t.apply p).1, b + (t.apply p).2)) '' S

def IsClassTransversal (G : List (List Int)) (C : Finset (Set Cell)) : Prop :=
  (∀ T ∈ C, IsIsland G T) ∧
    (∀ S, IsIsland G S → ∃ T ∈ C, IslandEquiv S T) ∧
    (∀ S ∈ C, ∀ T ∈ C, IslandEquiv S T → S = T)

def HasBlock (row : List Int) (L : ℕ) : Prop :=
  ∃ a : ℕ, 1 ≤ L ∧ a + L ≤ row.length ∧
    (∀ c, a ≤ c → c < a + L → row.getD c 0 = 1) ∧
    (a = 0 ∨ row.getD (a - 1) 0 = 0) ∧
    (a + L = row.length ∨ row.getD (a + L) 0 = 0)

noncomputable def numBlockLengths (row : List Int) : ℕ :=
  Nat.card { L : ℕ // HasBlock row L }

def rotate90 (m n : ℕ) (G : List (List Int)) : List (List Int) :=
  (List.range n).map (fun j => (List.range m).map (fun i => cellAt G (m - 1 - i) j))

def reflectLR (m n : ℕ) (G : List (List Int)) : List (List Int) :=
  (List.range m).map (fun i => (List.range n).map (fun j => cellAt G i (n - 1 - j)))

def transpose (m n : ℕ) (G : List (List Int)) : List (List Int) :=
  (List.range n).map (fun j => (List.range m).map (fun i => cellAt G i j))

def IsPadding (G G' : List (List Int)) : Prop :=
  ∃ d u l r : ℕ,
    G'.length = d + G.length + u ∧
      (∀ i, i < G.length → (rowAt G' (d + i)).length = l + (rowAt G i).length + r) ∧
      (∀ i j, cellAt G' i j =
        if d ≤ i ∧ i < d + G.length ∧ l ≤ j ∧ j < l + (rowAt G (i - d)).length
          then cellAt G (i - d) (j - l) else 0)

/-- Let a cell (i,j) be land when grid[i][j] = 1. Let an island be a maximal nonempty set of land cells that is 4-connected, where two cells are 4-adjacent when their row indices differ by 1 and their column indices are equal, or their column indices differ by 1 and their row indices are equal. Let I be the set of all islands. For two islands S and T, write S ~ T when there exist integers a,b and one of the eight maps f(x,y) = (x,y), (-y,x), (-x,-y), (y,-x), (-x,y), (x,-y), (y,x), (-y,-x) such that T = {(a + u, b + v) : (u,v) = f(i,j) for some (i,j) in S}. The function returns a result r and r is the number of equivalence classes of I under ~.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      ∃ C : Finset (Set Cell),
        IsClassTransversal (gridContents grid) C ∧ r.val = (C.card : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      ∃ C : Finset (Set Cell),
        IsClassTransversal (gridContents grid) C ∧ r.val = (C.card : ℤ)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r) := by
  sorry

/-- Let K be the number of islands of grid, where an island is a maximal nonempty 4-connected component of cells with grid[i][j] = 1. Whenever the function returns a result r, r is an integer with 0 <= r <= K.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∀ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (numIslands (gridContents grid) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∀ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      0 ≤ r.val ∧ r.val ≤ (numIslands (gridContents grid) : ℤ)) := by
  sorry

/-- Let L be the number of cells (i,j) with grid[i][j] = 1. The function returns a result r, and r = 0 if and only if L = 0.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = 0 ↔ numLand (gridContents grid) = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = 0 ↔ numLand (gridContents grid) = 0)) := by
  sorry

/-- If m = 1, then the function returns r equal to the number of distinct positive integers L for which the single row grid[0] has a maximal contiguous block of exactly L entries equal to 1. A maximal contiguous block is an interval [a,b] of column indices with 0 <= a <= b < n such that grid[0][c] = 1 for every a <= c <= b, and (a = 0 or grid[0][a-1] = 0) and (b = n-1 or grid[0][b+1] = 0).
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) (hm : m = 1) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      r.val = (numBlockLengths (rowAt (gridContents grid) 0) : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) (hm : m = 1), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      r.val = (numBlockLengths (rowAt (gridContents grid) 0) : ℤ)) := by
  sorry

/-- Define an island as a maximal nonempty 4-connected component of cells with grid[i][j] = 1. Define two islands S and T to be equivalent when one can be carried to the other by a translation followed by one of the eight symmetries of the square (the four rotations by 0, 90, 180, 270 degrees and the four reflections in the horizontal, vertical, main-diagonal, and anti-diagonal axes). If the set of islands is nonempty and any two islands in it are equivalent, then the function returns r = 1.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n)
    (hne : ∃ S : Set Cell, IsIsland (gridContents grid) S)
    (hall : ∀ S T : Set Cell, IsIsland (gridContents grid) S →
      IsIsland (gridContents grid) T → IslandEquiv S T) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n)
    (hne : ∃ S : Set Cell, IsIsland (gridContents grid) S)
    (hall : ∀ S T : Set Cell, IsIsland (gridContents grid) S →
      IsIsland (gridContents grid) T → IslandEquiv S T), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧ r.val = 1) := by
  sorry

/-- Define an island as a maximal nonempty 4-connected component of cells with grid[i][j] = 1. Define two islands S and T to be equivalent when one can be carried to the other by a translation followed by one of the eight symmetries of the square (the four rotations by 0, 90, 180, 270 degrees and the four reflections in the horizontal, vertical, main-diagonal, and anti-diagonal axes). Let K be the number of islands. If no two distinct islands of grid are equivalent, then the function returns r = K.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n)
    (hdisj : ∀ S T : Set Cell, IsIsland (gridContents grid) S →
      IsIsland (gridContents grid) T → IslandEquiv S T → S = T) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      r.val = (numIslands (gridContents grid) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n)
    (hdisj : ∀ S T : Set Cell, IsIsland (gridContents grid) S →
      IsIsland (gridContents grid) T → IslandEquiv S T → S = T), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      r.val = (numIslands (gridContents grid) : ℤ)) := by
  sorry

/-- Let G be the input grid with m rows and n columns. Let Grot be its 90-degree clockwise rotation, the n by m grid defined by Grot[j][m-1-i] = grid[i][j] for all 0 <= i < m and 0 <= j < n. The function returns the same result on Grot as on grid: if r is the result for grid and r' is the result for Grot, then r = r'.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_8 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (hrot : gridContents grid' = rotate90 m n (gridContents grid)) :
    ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (hrot : gridContents grid' = rotate90 m n (gridContents grid)), ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val) := by
  sorry

/-- Let Gref be the left/right reflection of the input grid, defined by Gref[i][j] = grid[i][n-1-j] for 0 <= i < m and 0 <= j < n. The function returns the same result on Gref as on grid.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (href : gridContents grid' = reflectLR m n (gridContents grid)) :
    ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (href : gridContents grid' = reflectLR m n (gridContents grid)), ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val) := by
  sorry

/-- Let G' be any grid obtained from grid by adding zero or more all-zero rows above and below it and zero or more all-zero columns to its left and right, and assume G' still satisfies the preconditions. Then the function returns the same result on G' as on grid.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_10 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (hpad : IsPadding (gridContents grid) (gridContents grid')) :
    ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (hpad : IsPadding (gridContents grid) (gridContents grid')), ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val) := by
  sorry

/-- Let Gtrans be the transpose of the input grid, the n by m grid defined by Gtrans[j][i] = grid[i][j] for all 0 <= i < m and 0 <= j < n. The function returns the same result on Gtrans as on grid.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_11 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (htrans : gridContents grid' = transpose m n (gridContents grid)) :
    ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n m' n' : ℕ)
    (hpre : IsBitGrid grid m n) (hpre' : IsBitGrid grid' m' n')
    (htrans : gridContents grid' = transpose m n (gridContents grid)), ∀ r r' : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r →
      Aegis.NumDistinctIslands2.num_distinct_islands2 grid' = ok r' → r.val = r'.val) := by
  sorry

/-- Let I be the set of all islands (maximal nonempty 4-connected components of cells with grid[i][j] = 1), and define equivalence of islands by translation followed by one of the eight symmetries of the square. The function returns a result r, and r = 1 if and only if I is nonempty and any two islands in I are equivalent.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = 1 ↔
        (∃ S : Set Cell, IsIsland (gridContents grid) S) ∧
          ∀ S T : Set Cell, IsIsland (gridContents grid) S →
            IsIsland (gridContents grid) T → IslandEquiv S T) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = 1 ↔
        (∃ S : Set Cell, IsIsland (gridContents grid) S) ∧
          ∀ S T : Set Cell, IsIsland (gridContents grid) S →
            IsIsland (gridContents grid) T → IslandEquiv S T)) := by
  sorry

/-- Let K be the number of islands, where an island is a maximal nonempty 4-connected component of cells with grid[i][j] = 1, and define equivalence of islands by translation followed by one of the eight symmetries of the square. The function returns a result r, and r = K if and only if no two distinct islands of grid are equivalent.
  Preconditions: Let m = len(grid). There is an integer n such that 1 <= m <= 50, 1 <= n <= 50, len(grid[i]) = n for every 0 <= i < m, and grid[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. Cells outside the grid are treated as water. -/
theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n) :
    ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = (numIslands (gridContents grid) : ℤ) ↔
        ∀ S T : Set Cell, IsIsland (gridContents grid) S →
          IsIsland (gridContents grid) T → IslandEquiv S T → S = T) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
    (hpre : IsBitGrid grid m n), ∃ r : I64, Aegis.NumDistinctIslands2.num_distinct_islands2 grid = ok r ∧
      (r.val = (numIslands (gridContents grid) : ℤ) ↔
        ∀ S T : Set Cell, IsIsland (gridContents grid) S →
          IsIsland (gridContents grid) T → IslandEquiv S T → S = T)) := by
  sorry

end AegisSpec.NumDistinctIslands2
