import Aegis.MinimumMoves.Code.Funs

/-!
# Specifications of `Aegis.MinimumMoves.minimum_moves`

LeetCode problem `minimum-moves-to-reach-target-with-rotations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumMoves

def rowCells (v : alloc.vec.Vec Std.I64) : List Int :=
  v.slice.list.toList.map (fun x => x.val)

def gridRows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
  grid.list.toList.map rowCells

def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ((gridRows grid).getD i []).getD j 0

def rowLength (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((gridRows grid).getD i []).length

def GridOK (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  2 ≤ n ∧ n ≤ 100 ∧ grid.leng = n ∧
    (∀ i, i < n → rowLength grid i = n) ∧
    (∀ i j, i < n → j < n → entry grid i j = 0 ∨ entry grid i j = 1) ∧
    entry grid 0 0 = 0 ∧ entry grid 0 1 = 0

inductive Orient where
  | H
  | V
  deriving DecidableEq, Repr

structure SnakeConfig where
  r : Nat
  c : Nat
  o : Orient
  deriving DecidableEq, Repr

def SnakeConfig.cells (C : SnakeConfig) : List (Nat × Nat) :=
  match C.o with
  | Orient.H => [(C.r, C.c), (C.r, C.c + 1)]
  | Orient.V => [(C.r, C.c), (C.r + 1, C.c)]

def ValidConfig (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (C : SnakeConfig) : Prop :=
  ∀ p ∈ C.cells, p.1 < n ∧ p.2 < n ∧ entry grid p.1 p.2 = 0

def StraightStep (n : Nat) (C C' : SnakeConfig) : Prop :=
  (∃ r c, C = ⟨r, c, Orient.H⟩ ∧ C' = ⟨r, c + 1, Orient.H⟩ ∧ c + 2 < n) ∨
  (∃ r c, C = ⟨r, c, Orient.V⟩ ∧ C' = ⟨r, c + 1, Orient.V⟩ ∧ c + 1 < n) ∨
  (∃ r c, C = ⟨r, c, Orient.H⟩ ∧ C' = ⟨r + 1, c, Orient.H⟩ ∧ r + 1 < n) ∨
  (∃ r c, C = ⟨r, c, Orient.V⟩ ∧ C' = ⟨r + 1, c, Orient.V⟩ ∧ r + 2 < n)

def RotStep (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (C C' : SnakeConfig) : Prop :=
  (∃ r c, C = ⟨r, c, Orient.H⟩ ∧ C' = ⟨r, c, Orient.V⟩ ∧ r + 1 < n ∧
      entry grid (r + 1) (c + 1) = 0) ∨
    (∃ r c, C = ⟨r, c, Orient.V⟩ ∧ C' = ⟨r, c, Orient.H⟩ ∧ c + 1 < n ∧
      entry grid (r + 1) (c + 1) = 0)

def ValidMove (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (C C' : SnakeConfig) : Prop :=
  ValidConfig grid n C ∧ ValidConfig grid n C' ∧
    (StraightStep n C C' ∨ RotStep grid n C C')

def StraightMove (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (C C' : SnakeConfig) : Prop :=
  ValidConfig grid n C ∧ ValidConfig grid n C' ∧ StraightStep n C C'

inductive ReachExact (R : SnakeConfig → SnakeConfig → Prop) :
    Nat → SnakeConfig → SnakeConfig → Prop where
  | refl (C : SnakeConfig) : ReachExact R 0 C C
  | step {k : Nat} {C C' C'' : SnakeConfig} :
      R C C' → ReachExact R k C' C'' → ReachExact R (k + 1) C C''

def startConfig : SnakeConfig := ⟨0, 0, Orient.H⟩

def targetConfig (n : Nat) : SnakeConfig := ⟨n - 1, n - 2, Orient.H⟩

def ReachesAll (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  ∃ d, ReachExact (ValidMove grid n) d startConfig (targetConfig n)

def ReachesStraight (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
  ∃ d, ReachExact (StraightMove grid n) d startConfig (targetConfig n)

def MinLenAll (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (d : Nat) : Prop :=
  ReachExact (ValidMove grid n) d startConfig (targetConfig n) ∧
    ∀ d', d' < d → ¬ ReachExact (ValidMove grid n) d' startConfig (targetConfig n)

/-- The function returns a result r (it does not fail). Define a configuration as a triple (r, c, o) with o in {H, V}: H(r,c) means the snake occupies cells (r,c) and (r,c+1); V(r,c) means it occupies (r,c) and (r+1,c). A configuration is valid if both cells are inside the n*n grid and have grid value 0. A valid move leads from valid C to valid C' if: (1) right: H(r,c)->H(r,c+1) when c+2<n, or V(r,c)->V(r,c+1) when c+1<n; (2) down: H(r,c)->H(r+1,c) when r+1<n, or V(r,c)->V(r+1,c) when r+2<n; (3) clockwise rotation: H(r,c)->V(r,c) when r+1<n; (4) counterclockwise rotation: V(r,c)->H(r,c) when c+1<n; in every case every cell of C' must be empty (grid value 0); additionally, clockwise rotation requires (r+1,c+1) to be empty, and counterclockwise rotation requires (r+1,c+1) to be empty. The start configuration is H(0,0) and the target configuration is H(n-1,n-2). If there exists a finite sequence of valid moves from start to target, then r is the minimum length of such a sequence. Otherwise, r = -1.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n) :
    ∃ rv : Std.I64,
      Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
        (ReachesAll grid n → ∃ d, MinLenAll grid n d ∧ rv.val = (d : Int)) ∧
        (¬ ReachesAll grid n → rv.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n), ∃ rv : Std.I64,
      Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
        (ReachesAll grid n → ∃ d, MinLenAll grid n d ∧ rv.val = (d : Int)) ∧
        (¬ ReachesAll grid n → rv.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail (no panic, no overflow, no out-of-bounds indexing).
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n) :
    ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n), ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv) := by
  sorry

/-- If the function returns a result r with r != -1, then 2*n - 3 <= r <= 2*n*(n-1) - 1.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv) (hne : rv.val ≠ -1) :
    2 * (n : Int) - 3 ≤ rv.val ∧ rv.val ≤ 2 * (n : Int) * ((n : Int) - 1) - 1 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv) (hne : rv.val ≠ -1), 2 * (n : Int) - 3 ≤ rv.val ∧ rv.val ≤ 2 * (n : Int) * ((n : Int) - 1) - 1) := by
  sorry

/-- If the function returns a result r with r >= 0, then r is odd.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv) (hpos : 0 ≤ rv.val) :
    ∃ k : Int, rv.val = 2 * k + 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv) (hpos : 0 ≤ rv.val), ∃ k : Int, rv.val = 2 * k + 1) := by
  sorry

/-- If grid[n-1][n-2] = 1 or grid[n-1][n-1] = 1, then the function returns -1.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hblocked : entry grid (n - 1) (n - 2) = 1 ∨ entry grid (n - 1) (n - 1) = 1) :
    ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = -1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hblocked : entry grid (n - 1) (n - 2) = 1 ∨ entry grid (n - 1) (n - 1) = 1), ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = -1) := by
  sorry

/-- If grid[i][j] = 0 for every i, j with 0 <= i < n and 0 <= j < n, then the function returns 2*n - 3.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hempty : ∀ i j, i < n → j < n → entry grid i j = 0) :
    ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
      rv.val = 2 * (n : Int) - 3 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hempty : ∀ i j, i < n → j < n → entry grid i j = 0), ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
      rv.val = 2 * (n : Int) - 3) := by
  sorry

/-- If n = 2, then the function returns 1 when grid[1][0] = 0 and grid[1][1] = 0, and returns -1 otherwise.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hn : n = 2) :
    ((entry grid 1 0 = 0 ∧ entry grid 1 1 = 0 →
        ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = 1) ∧
      (¬ (entry grid 1 0 = 0 ∧ entry grid 1 1 = 0) →
        ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = -1)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hn : n = 2), ((entry grid 1 0 = 0 ∧ entry grid 1 1 = 0 →
        ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = 1) ∧
      (¬ (entry grid 1 0 = 0 ∧ entry grid 1 1 = 0) →
        ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧ rv.val = -1))) := by
  sorry

/-- If the function returns a result r, then r != 0.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv) : rv.val ≠ 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv), rv.val ≠ 0) := by
  sorry

/-- Let r = minimum_moves(grid) and r' = minimum_moves(grid'). If r' != -1, then r != -1 and r <= r'. If r = -1, then r' = -1.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. Let grid' be another n×n grid satisfying the same constraints (entries 0 or 1, grid'[0][0]=0, grid'[0][1]=0) such that for every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] <= grid'[i][j]. -/
theorem spec_9 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : GridOK grid n) (h' : GridOK grid' n)
    (hle : ∀ i j, i < n → j < n → entry grid i j ≤ entry grid' i j) :
    ∃ rv rv' : Std.I64,
      Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
        Aegis.MinimumMoves.minimum_moves grid' = ok rv' ∧
        ((rv'.val ≠ -1 → rv.val ≠ -1 ∧ rv.val ≤ rv'.val) ∧
          (rv.val = -1 → rv'.val = -1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (n : Nat)
    (h : GridOK grid n) (h' : GridOK grid' n)
    (hle : ∀ i j, i < n → j < n → entry grid i j ≤ entry grid' i j), ∃ rv rv' : Std.I64,
      Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
        Aegis.MinimumMoves.minimum_moves grid' = ok rv' ∧
        ((rv'.val ≠ -1 → rv.val ≠ -1 ∧ rv.val ≤ rv'.val) ∧
          (rv.val = -1 → rv'.val = -1))) := by
  sorry

/-- If there exists a sequence of valid moves from H(0,0) to H(n-1,n-2) that uses only right moves and down moves (no rotations), then the function returns 2*n - 3.
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hreach : ReachesStraight grid n) :
    ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
      rv.val = 2 * (n : Int) - 3 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (hreach : ReachesStraight grid n), ∃ rv : Std.I64, Aegis.MinimumMoves.minimum_moves grid = ok rv ∧
      rv.val = 2 * (n : Int) - 3) := by
  sorry

/-- If the function returns a result r with r = 2*n - 3, then there exists a sequence of valid moves from H(0,0) to H(n-1,n-2) that uses only right moves and down moves (no rotations).
  Preconditions: Let n = len(grid). 2 <= n <= 100. For every i with 0 <= i < n, len(grid[i]) = n. For every i, j with 0 <= i < n and 0 <= j < n, grid[i][j] is 0 or 1. grid[0][0] = 0 and grid[0][1] = 0. -/
theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv)
    (hrv : rv.val = 2 * (n : Int) - 3) :
    ReachesStraight grid n := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (h : GridOK grid n)
    (rv : Std.I64) (hr : Aegis.MinimumMoves.minimum_moves grid = ok rv)
    (hrv : rv.val = 2 * (n : Int) - 3), ReachesStraight grid n) := by
  sorry

end AegisSpec.MinimumMoves
