import Aegis.UniquePathsIii.Code.Funs

/-!
# Specifications of `Aegis.UniquePathsIii.unique_paths_iii`

LeetCode problem `unique-paths-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.UniquePathsIii

  namespace AegisSpec.UniquePathsIii

  abbrev Grid : Type := Slice (alloc.vec.Vec Std.I64)

  def rows (grid : Grid) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun x => x.val))

  def m (grid : Grid) : Nat := (rows grid).length

  def row (grid : Grid) (i : Nat) : List Int := (rows grid).getD i []

  def n (grid : Grid) : Nat := (row grid 0).length

  def cell (grid : Grid) (i j : Nat) : Int := (row grid i).getD j (-1)

  def cells (grid : Grid) : Finset (Nat × Nat) :=
    Finset.range (m grid) ×ˢ Finset.range (n grid)

  def nonObstacle (grid : Grid) : Finset (Nat × Nat) :=
    (cells grid).filter (fun c => cell grid c.1 c.2 ≠ -1)

  def K (grid : Grid) : Nat := (nonObstacle grid).card

  def freeCols (grid : Grid) (i : Nat) : Finset Nat :=
    (Finset.range (n grid)).filter (fun j => cell grid i j ≠ -1)

  def freeRows (grid : Grid) (j : Nat) : Finset Nat :=
    (Finset.range (m grid)).filter (fun i => cell grid i j ≠ -1)

  def manhattan (a b : Nat × Nat) : Nat :=
    ((a.1 : Int) - (b.1 : Int)).natAbs + ((a.2 : Int) - (b.2 : Int)).natAbs

  def setMin (s : Finset Nat) : Nat := if h : s.Nonempty then s.min' h else 0

  def setMax (s : Finset Nat) : Nat := if h : s.Nonempty then s.max' h else 0

  def adjacent (grid : Grid) (a b : Nat × Nat) : Prop :=
    a ∈ nonObstacle grid ∧ b ∈ nonObstacle grid ∧ manhattan a b = 1

  inductive Reach (grid : Grid) : Nat × Nat → Nat × Nat → Prop
    | refl (a : Nat × Nat) : Reach grid a a
    | step {a b c : Nat × Nat} : Reach grid a b → adjacent grid b c → Reach grid a c

  def connected (grid : Grid) : Prop :=
    ∀ a ∈ nonObstacle grid, ∀ b ∈ nonObstacle grid, Reach grid a b

  def degree (grid : Grid) (v : Nat × Nat) : Nat :=
    ((nonObstacle grid).filter (fun w => manhattan v w = 1)).card

  def adjacentDel (grid : Grid) (v a b : Nat × Nat) : Prop :=
    adjacent grid a b ∧ a ≠ v ∧ b ≠ v

  inductive ReachDel (grid : Grid) (v : Nat × Nat) : Nat × Nat → Nat × Nat → Prop
    | refl (a : Nat × Nat) : ReachDel grid v a a
    | step {a b c : Nat × Nat} : ReachDel grid v a b → adjacentDel grid v b c → ReachDel grid v a c

  noncomputable def componentOf (grid : Grid) (v a : Nat × Nat) : Finset (Nat × Nat) := by
    classical
    exact ((nonObstacle grid).erase v).filter (fun b => ReachDel grid v a b)

  noncomputable def numComponentsAfterDelete (grid : Grid) (v : Nat × Nat) : Nat :=
    (((nonObstacle grid).erase v).image (fun a => componentOf grid v a)).card

  abbrev Pos (grid : Grid) : Type := Fin (m grid) × Fin (n grid)

  def posToPair {grid : Grid} (c : Pos grid) : Nat × Nat := (c.1.val, c.2.val)

  def IsHamiltonianWalk (grid : Grid) (start finish : Pos grid)
      (p : Fin (K grid) → Pos grid) : Prop :=
    (∀ (h : 0 < K grid), p ⟨0, h⟩ = start) ∧
    (∀ (h : K grid - 1 < K grid), p ⟨K grid - 1, h⟩ = finish) ∧
    (∀ t : Fin (K grid), cell grid (p t).1.val (p t).2.val ≠ -1) ∧
    (∀ (t : Nat) (h : t + 1 < K grid),
      manhattan (posToPair (p ⟨t, Nat.lt_of_succ_lt h⟩)) (posToPair (p ⟨t + 1, h⟩)) = 1) ∧
    (∀ c : Pos grid, cell grid c.1.val c.2.val ≠ -1 → ∃! t : Fin (K grid), p t = c)

  noncomputable def numHamiltonianWalks (grid : Grid) (start finish : Pos grid) : Nat := by
    classical
    exact (Finset.univ.filter (fun p : Fin (K grid) → Pos grid =>
      IsHamiltonianWalk grid start finish p)).card

  structure GridSpec (grid : Grid) (sr sc er ec : Nat) : Prop where

    m_pos : 1 ≤ m grid

    n_pos : 1 ≤ n grid

    size_le : m grid * n grid ≤ 20

    row_len : ∀ i, i < m grid → (row grid i).length = n grid

    entry_val : ∀ i j, i < m grid → j < n grid →
      cell grid i j = -1 ∨ cell grid i j = 0 ∨ cell grid i j = 1 ∨ cell grid i j = 2

    start_row : sr < m grid

    start_col : sc < n grid

    start_val : cell grid sr sc = 1

    start_unique : ∀ i j, i < m grid → j < n grid → cell grid i j = 1 → i = sr ∧ j = sc

    end_row : er < m grid

    end_col : ec < n grid

    end_val : cell grid er ec = 2

    end_unique : ∀ i j, i < m grid → j < n grid → cell grid i j = 2 → i = er ∧ j = ec

  namespace GridSpec

  variable {grid : Grid} {sr sc er ec : Nat}

  def startPos (h : GridSpec grid sr sc er ec) : Pos grid :=
    (⟨sr, h.start_row⟩, ⟨sc, h.start_col⟩)

  def endPos (h : GridSpec grid sr sc er ec) : Pos grid :=
    (⟨er, h.end_row⟩, ⟨ec, h.end_col⟩)

  end GridSpec

  /-- The function returns a result r and r equals the number of sequences (r_0,c_0),...,(r_{K-1},c_{K-1}) such that: (1) (r_0,c_0) = (sr,sc) and (r_{K-1},c_{K-1}) = (er,ec); (2) for every t with 0 <= t < K, 0 <= r_t < m, 0 <= c_t < n, and grid[r_t][c_t] != -1; (3) for every t with 0 <= t < K-1, |r_{t+1}-r_t| + |c_{t+1}-c_t| = 1; (4) for every non-obstacle cell (i,j), there is exactly one t with (r_t,c_t) = (i,j). In other words, r is the number of 4-directional walks from the start to the end that visit every non-obstacle cell exactly once.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 (the start) and exactly one cell (er,ec) with grid[er][ec] = 2 (the end). A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells (so K >= 2). -/
  theorem spec_1 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
        r.val = ((numHamiltonianWalks grid h.startPos h.endPos : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
          r.val = ((numHamiltonianWalks grid h.startPos h.endPos : Nat) : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail: no panic, out-of-bounds access, or 64-bit overflow) for every grid satisfying the preconditions.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_2 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec), ∃ r : Std.I64, unique_paths_iii grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= (K-2)! (ordinary factorial; K >= 2). Equivalently, r is non-negative and is at most the number of permutations of the K-2 non-obstacle cells other than the start and end.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_3 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec) :
      ∀ r : Std.I64, unique_paths_iii grid = ok r →
        0 ≤ r.val ∧ r.val ≤ ((K grid - 2).factorial : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec), ∀ r : Std.I64, unique_paths_iii grid = ok r →
          0 ≤ r.val ∧ r.val ≤ ((K grid - 2).factorial : Int)) := by
    sorry

  /-- The function returns r, and r = 1 if |sr-er| + |sc-ec| = 1 (the start and end are 4-adjacent), and r = 0 otherwise.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. In addition, K = 2, so the only non-obstacle cells are the start and the end. -/
  theorem spec_4 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hK : K grid = 2) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
        r.val = (if manhattan (sr, sc) (er, ec) = 1 then (1 : Int) else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hK : K grid = 2), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
          r.val = (if manhattan (sr, sc) (er, ec) = 1 then (1 : Int) else 0)) := by
    sorry

  /-- The function returns r, and r = 1 if |sr-ur| + |sc-uc| = 1 and |er-ur| + |ec-uc| = 1, and r = 0 otherwise.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. In addition, K = 3; let (ur,uc) be the unique non-obstacle cell that is neither the start nor the end (so grid[ur][uc] = 0). -/
  theorem spec_5 {grid : Grid} {sr sc er ec ur uc : Nat} (h : GridSpec grid sr sc er ec)
      (hK : K grid = 3)
      (hur : ur < m grid) (huc : uc < n grid) (hval : cell grid ur uc = 0)
      (hmid : ∀ i j, i < m grid → j < n grid → cell grid i j ≠ -1 →
        (i = sr ∧ j = sc) ∨ (i = er ∧ j = ec) ∨ (i = ur ∧ j = uc)) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
        r.val = (if manhattan (sr, sc) (ur, uc) = 1 ∧ manhattan (er, ec) (ur, uc) = 1
          then (1 : Int) else 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec ur uc : Nat} (h : GridSpec grid sr sc er ec)
        (hK : K grid = 3)
        (hur : ur < m grid) (huc : uc < n grid) (hval : cell grid ur uc = 0)
        (hmid : ∀ i j, i < m grid → j < n grid → cell grid i j ≠ -1 →
          (i = sr ∧ j = sc) ∨ (i = er ∧ j = ec) ∨ (i = ur ∧ j = uc)), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
          r.val = (if manhattan (sr, sc) (ur, uc) = 1 ∧ manhattan (er, ec) (ur, uc) = 1
            then (1 : Int) else 0)) := by
    sorry

  /-- The function returns r, and r = 1 if S = {c | a <= c <= b} and {sc,ec} = {a,b}; otherwise r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. In addition, m = 1. Let S = {c | 0 <= c < n and grid[0][c] != -1}, let a = min S, and let b = max S. The start column is sc and the end column is ec (both rows are 0). -/
  theorem spec_6 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hm : m grid = 1) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
        r.val = (if freeCols grid 0 = Finset.Icc (setMin (freeCols grid 0)) (setMax (freeCols grid 0)) ∧
              ({sc, ec} : Finset Nat) = {setMin (freeCols grid 0), setMax (freeCols grid 0)}
            then (1 : Int) else 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hm : m grid = 1), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
          r.val = (if freeCols grid 0 = Finset.Icc (setMin (freeCols grid 0)) (setMax (freeCols grid 0)) ∧
                ({sc, ec} : Finset Nat) = {setMin (freeCols grid 0), setMax (freeCols grid 0)}
              then (1 : Int) else 0)) := by
    sorry

  /-- The function returns r, and r = 1 if S = {i | a <= i <= b} and {sr,er} = {a,b}; otherwise r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. In addition, n = 1. Let S = {i | 0 <= i < m and grid[i][0] != -1}, let a = min S, and let b = max S. The start row is sr and the end row is er (both columns are 0). -/
  theorem spec_7 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hn : n grid = 1) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
        r.val = (if freeRows grid 0 = Finset.Icc (setMin (freeRows grid 0)) (setMax (freeRows grid 0)) ∧
              ({sr, er} : Finset Nat) = {setMin (freeRows grid 0), setMax (freeRows grid 0)}
            then (1 : Int) else 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hn : n grid = 1), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧
          r.val = (if freeRows grid 0 = Finset.Icc (setMin (freeRows grid 0)) (setMax (freeRows grid 0)) ∧
                ({sr, er} : Finset Nat) = {setMin (freeRows grid 0), setMax (freeRows grid 0)}
              then (1 : Int) else 0)) := by
    sorry

  /-- If either (K is even and (sr+sc) mod 2 = (er+ec) mod 2) or (K is odd and (sr+sc) mod 2 != (er+ec) mod 2), then the function returns r with r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_8 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hpar : (K grid % 2 = 0 ∧ (sr + sc) % 2 = (er + ec) % 2) ∨
              (K grid % 2 = 1 ∧ (sr + sc) % 2 ≠ (er + ec) % 2)) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hpar : (K grid % 2 = 0 ∧ (sr + sc) % 2 = (er + ec) % 2) ∨
                (K grid % 2 = 1 ∧ (sr + sc) % 2 ≠ (er + ec) % 2)), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0) := by
    sorry

  /-- Let G be the undirected graph whose vertices are the non-obstacle cells, with an edge between two vertices exactly when the corresponding cells are 4-adjacent. If G is not connected, then the function returns r with r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_9 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hconn : ¬ connected grid) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hconn : ¬ connected grid), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0) := by
    sorry

  /-- Let G be the graph on non-obstacle cells with 4-adjacency edges. If G has a non-obstacle cell that is neither the start nor the end and has degree less than 2, or has the start or the end with degree less than 1, then the function returns r with r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_10 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hdeg : (∃ c ∈ nonObstacle grid, c ≠ (sr, sc) ∧ c ≠ (er, ec) ∧ degree grid c < 2) ∨
              degree grid (sr, sc) < 1 ∨ degree grid (er, ec) < 1) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hdeg : (∃ c ∈ nonObstacle grid, c ≠ (sr, sc) ∧ c ≠ (er, ec) ∧ degree grid c < 2) ∨
                degree grid (sr, sc) < 1 ∨ degree grid (er, ec) < 1), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0) := by
    sorry

  /-- Let grid' be the grid obtained from grid by replacing every 1 by 2 and every 2 by 1 (all other entries unchanged). Let r be the result of the function on grid and r' the result on grid'. Then the function returns both results and r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_11 {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hswap : rows grid' = (rows grid).map
        (List.map (fun x => if x = 1 then 2 else if x = 2 then 1 else x))) :
      ∃ r r' : Std.I64,
        unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hswap : rows grid' = (rows grid).map
          (List.map (fun x => if x = 1 then 2 else if x = 2 then 1 else x))), ∃ r r' : Std.I64,
          unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let grid^T be the n by m transpose of grid, defined by grid^T[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Let r and r' be the results of the function on grid and grid^T respectively. Then r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_12 {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hT : rows grid' = (rows grid).transpose) :
      ∃ r r' : Std.I64,
        unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hT : rows grid' = (rows grid).transpose), ∃ r r' : Std.I64,
          unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let grid' be the m by n grid defined by grid'[i][j] = grid[i][n-1-j] for 0 <= i < m and 0 <= j < n. Let r and r' be the results of the function on grid and grid' respectively. Then r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_13 {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hflip : rows grid' = (rows grid).map List.reverse) :
      ∃ r r' : Std.I64,
        unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hflip : rows grid' = (rows grid).map List.reverse), ∃ r r' : Std.I64,
          unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let grid' be the m by n grid defined by grid'[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Let r and r' be the results of the function on grid and grid' respectively. Then r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_14 {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hrot : rows grid' = (rows grid).reverse.map List.reverse) :
      ∃ r r' : Std.I64,
        unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ {grid grid' : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hrot : rows grid' = (rows grid).reverse.map List.reverse), ∃ r r' : Std.I64,
          unique_paths_iii grid = ok r ∧ unique_paths_iii grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let G be the undirected graph whose vertices are the non-obstacle cells, with an edge between two vertices exactly when the corresponding cells are 4-adjacent. For a non-obstacle cell v, let c(v) be the number of connected components of the graph obtained from G by deleting v and all its incident edges (on the remaining non-obstacle cells). If v is the start or the end and c(v) > 1, or v is neither the start nor the end and c(v) > 2, then the function returns a result r with r = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m >= 1, n >= 1, m*n <= 20; every row grid[i] has length n; every entry grid[i][j] is one of -1, 0, 1, 2; there is exactly one cell (sr,sc) with grid[sr][sc] = 1 and exactly one cell (er,ec) with grid[er][ec] = 2. A non-obstacle cell is any (i,j) with grid[i][j] != -1; let K be the number of non-obstacle cells. -/
  theorem spec_15 {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
      (hcut : numComponentsAfterDelete grid (sr, sc) > 1 ∨
              numComponentsAfterDelete grid (er, ec) > 1 ∨
              (∃ c ∈ nonObstacle grid, c ≠ (sr, sc) ∧ c ≠ (er, ec) ∧
                numComponentsAfterDelete grid c > 2)) :
      ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ {grid : Grid} {sr sc er ec : Nat} (h : GridSpec grid sr sc er ec)
        (hcut : numComponentsAfterDelete grid (sr, sc) > 1 ∨
                numComponentsAfterDelete grid (er, ec) > 1 ∨
                (∃ c ∈ nonObstacle grid, c ≠ (sr, sc) ∧ c ≠ (er, ec) ∧
                  numComponentsAfterDelete grid c > 2)), ∃ r : Std.I64, unique_paths_iii grid = ok r ∧ r.val = 0) := by
    sorry

  end AegisSpec.UniquePathsIii
