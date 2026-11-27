import Aegis.CountPaths.Code.Funs

/-!
# Specifications of `Aegis.CountPaths.count_paths`

LeetCode problem `number-of-increasing-paths-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountPaths

  namespace AegisSpec.CountPaths

  def gridVals (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    grid.val.map (fun row => row.val.map (fun v => v.val))

  def listCellAt (g : List (List Int)) (i j : Nat) : Option Int :=
    match g[i]? with
    | some row => row[j]?
    | none => none

  def cellAt (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    listCellAt (gridVals grid) i j

  def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    match gridVals grid with
    | [] => 0
    | row :: _ => row.length

  def Rect (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    grid.val.length = m ∧
      ∀ (i : Nat) (row : alloc.vec.Vec Std.I64), i < m → grid.val[i]? = some row →
        row.val.length = n

  def ValRange (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    ∀ (i j : Nat) (v : Int), i < m → j < n → cellAt grid i j = some v → 1 ≤ v ∧ v ≤ 100000

  def adjacentB (p q : Nat × Nat) : Bool :=
    (Int.natAbs ((p.1 : Int) - (q.1 : Int)) + Int.natAbs ((p.2 : Int) - (q.2 : Int))) == 1

  def adjacentChainB : List (Nat × Nat) → Bool
    | [] => true
    | [_] => true
    | p :: q :: rest => adjacentB p q && adjacentChainB (q :: rest)

  def strictlyIncrB : List Int → Bool
    | [] => true
    | [_] => true
    | a :: b :: rest => decide (a < b) && strictlyIncrB (b :: rest)

  def pathValues (g : List (List Int)) (l : List (Nat × Nat)) : List Int :=
    l.filterMap (fun p => listCellAt g p.1 p.2)

  def strictIncrValuesB (g : List (List Int)) (l : List (Nat × Nat)) : Bool :=
    ((pathValues g l).length == l.length) && strictlyIncrB (pathValues g l)

  def isIncPathB (g : List (List Int)) (m n : Nat) (l : List (Nat × Nat)) : Bool :=
    (!l.isEmpty) && l.all (fun p => decide (p.1 < m) && decide (p.2 < n)) &&
      adjacentChainB l && strictIncrValuesB g l

  def Adjacent (p q : Nat × Nat) : Prop := adjacentB p q = true

  def AdjacentChain (l : List (Nat × Nat)) : Prop := adjacentChainB l = true

  def StrictIncrValues (g : List (List Int)) (l : List (Nat × Nat)) : Prop :=
    strictIncrValuesB g l = true

  def IsIncPath (g : List (List Int)) (m n : Nat) (l : List (Nat × Nat)) : Prop :=
    isIncPathB g m n l = true

  def cellFinset (m n : Nat) : Finset (Nat × Nat) := (Finset.range m).product (Finset.range n)

  def listsOfLen {α : Type} [DecidableEq α] (s : Finset α) : Nat → Finset (List α)
    | 0 => {[]}
    | k + 1 => s.biUnion (fun a => (listsOfLen s k).image (fun l => a :: l))

  def listsUpToLen {α : Type} [DecidableEq α] (s : Finset α) (k : Nat) : Finset (List α) :=
    (Finset.range (k + 1)).biUnion (fun i => listsOfLen s i)

  def valueLtB (g : List (List Int)) (p q : Nat × Nat) : Bool :=
    match listCellAt g p.1 p.2, listCellAt g q.1 q.2 with
    | some v, some w => decide (v < w)
    | _, _ => false

  def numIncPaths (g : List (List Int)) (m n : Nat) : Nat :=
    ((listsUpToLen (cellFinset m n) (m * n)).filter (fun l => isIncPathB g m n l)).card

  def numIncPathsFrom (g : List (List Int)) (m n : Nat) (p : Nat × Nat) : Nat :=
    ((listsUpToLen (cellFinset m n) (m * n)).filter
        (fun l => l.head? = some p && isIncPathB g m n l)).card

  def betterNeighbours (g : List (List Int)) (m n : Nat)
      (p : Nat × Nat) : Finset (Nat × Nat) :=
    (cellFinset m n).filter (fun q => adjacentB p q && valueLtB g p q)

  def C (grid : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    numIncPaths (gridVals grid) grid.val.length (rowLen grid)

  def D (grid : Slice (alloc.vec.Vec Std.I64)) (p : Nat × Nat) : Nat :=
    numIncPathsFrom (gridVals grid) grid.val.length (rowLen grid) p

  /-- Let M = 1000000007. A path in grid is a finite sequence of cells ((r_0,c_0),...,(r_k,c_k)) with k >= 0 such that 0 <= r_t < m and 0 <= c_t < n for all t, and for every t < k the cells (r_t,c_t) and (r_{t+1},c_{t+1}) are adjacent in one of the four directions, i.e. |r_{t+1}-r_t| + |c_{t+1}-c_t| = 1. Such a path is strictly increasing if grid[r_0][c_0] < grid[r_1][c_1] < ... < grid[r_k][c_k]. Let C(grid) be the number of strictly increasing paths (including all paths of length 1, i.e. k=0), with each cell sequence counted separately. The function returns a result r and r = C(grid) mod M, where mod denotes the unique remainder in {0,...,M-1}.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n) :
      ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((C grid % 1000000007 : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n), ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((C grid % 1000000007 : Nat) : Int)) := by
    sorry

  /-- Whenever count_paths(grid) returns a result r, 0 <= r < 1000000007.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n) :
      ∀ r : Std.I64, count_paths grid = ok r → 0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n), ∀ r : Std.I64, count_paths grid = ok r → 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- The function returns a result (there exists an i64 r such that count_paths(grid) = Result.ok r); it does not fail, panic, or signal arithmetic overflow or out-of-bounds on any input satisfying the precondition.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n) :
      ∃ r : Std.I64, count_paths grid = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n), ∃ r : Std.I64, count_paths grid = ok r) := by
    sorry

  /-- The function returns a result r and r = m * n.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume additionally that all entries of grid are equal: there is an integer c with grid[i][j] = c for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hconst : ∃ c : Int, ∀ i j : Nat, i < m → j < n → cellAt grid i j = some c) :
      ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((m * n : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hconst : ∃ c : Int, ∀ i j : Nat, i < m → j < n → cellAt grid i j = some c), ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((m * n : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r = n * (n + 1) / 2.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume m = 1 and for every j with 0 <= j < n-1, grid[0][j] < grid[0][j+1]. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hrow : m = 1)
      (hincr : ∀ j : Nat, j + 1 < n →
        ∃ v w : Int, cellAt grid 0 j = some v ∧ cellAt grid 0 (j + 1) = some w ∧ v < w) :
      ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((n * (n + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hrow : m = 1)
        (hincr : ∀ j : Nat, j + 1 < n →
          ∃ v w : Int, cellAt grid 0 j = some v ∧ cellAt grid 0 (j + 1) = some w ∧ v < w), ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((n * (n + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- The function returns a result r and r = m * (m + 1) / 2.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume n = 1 and for every i with 0 <= i < m-1, grid[i][0] < grid[i+1][0]. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hcol : n = 1)
      (hincr : ∀ i : Nat, i + 1 < m →
        ∃ v w : Int, cellAt grid i 0 = some v ∧ cellAt grid (i + 1) 0 = some w ∧ v < w) :
      ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((m * (m + 1) / 2 : Nat) : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hcol : n = 1)
        (hincr : ∀ i : Nat, i + 1 < m →
          ∃ v w : Int, cellAt grid i 0 = some v ∧ cellAt grid (i + 1) 0 = some w ∧ v < w), ∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((m * (m + 1) / 2 : Nat) : Int)) := by
    sorry

  /-- count_paths(grid) returns a result r, count_paths(grid') returns a result r', and r = r'.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Let f be any function from integers to integers that is strictly increasing (for all integers x < y, f(x) < f(y)). Let grid' be an m x n grid with grid'[i][j] = f(grid[i][j]) for all i,j, and assume grid' also satisfies the same problem constraints (in particular its entries lie in [1,100000]). -/
  theorem spec_7 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (f : Int → Int)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hrect' : Rect grid' m n)
      (hval' : ValRange grid' m n)
      (hf : ∀ x y : Int, x < y → f x < f y)
      (hmap : ∀ i j : Nat, i < m → j < n → cellAt grid' i j = (cellAt grid i j).map f) :
      ∃ r r' : Std.I64, count_paths grid = ok r ∧ count_paths grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (f : Int → Int)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hrect' : Rect grid' m n)
        (hval' : ValRange grid' m n)
        (hf : ∀ x y : Int, x < y → f x < f y)
        (hmap : ∀ i j : Nat, i < m → j < n → cellAt grid' i j = (cellAt grid i j).map f), ∃ r r' : Std.I64, count_paths grid = ok r ∧ count_paths grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- count_paths(grid) returns a result r, count_paths(T) returns a result r_T, and r = r_T.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Let T be the n x m grid defined by T[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid T : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hrectT : Rect T n m)
      (htranspose : ∀ i j : Nat, i < m → j < n → cellAt T j i = cellAt grid i j) :
      ∃ r rT : Std.I64, count_paths grid = ok r ∧ count_paths T = ok rT ∧ r.val = rT.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid T : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hrectT : Rect T n m)
        (htranspose : ∀ i j : Nat, i < m → j < n → cellAt T j i = cellAt grid i j), ∃ r rT : Std.I64, count_paths grid = ok r ∧ count_paths T = ok rT ∧ r.val = rT.val) := by
    sorry

  /-- count_paths(grid) returns a result r, count_paths(R) returns a result r_R, and r = r_R.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Let R be the m x n grid defined by R[i][j] = grid[m-1-i][j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (grid R : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hrectR : Rect R m n)
      (hrev : ∀ i j : Nat, i < m → j < n → cellAt R i j = cellAt grid (m - 1 - i) j) :
      ∃ r rR : Std.I64, count_paths grid = ok r ∧ count_paths R = ok rR ∧ r.val = rR.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid R : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hrectR : Rect R m n)
        (hrev : ∀ i j : Nat, i < m → j < n → cellAt R i j = cellAt grid (m - 1 - i) j), ∃ r rR : Std.I64, count_paths grid = ok r ∧ count_paths R = ok rR ∧ r.val = rR.val) := by
    sorry

  /-- count_paths(grid) returns a result r, count_paths(Cg) returns a result r_Cg, and r = r_Cg.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Let Cg be the m x n grid defined by Cg[i][j] = grid[i][n-1-j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid Cg : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hrectCg : Rect Cg m n)
      (hrev : ∀ i j : Nat, i < m → j < n → cellAt Cg i j = cellAt grid i (n - 1 - j)) :
      ∃ r rCg : Std.I64, count_paths grid = ok r ∧ count_paths Cg = ok rCg ∧ r.val = rCg.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid Cg : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hrectCg : Rect Cg m n)
        (hrev : ∀ i j : Nat, i < m → j < n → cellAt Cg i j = cellAt grid i (n - 1 - j)), ∃ r rCg : Std.I64, count_paths grid = ok r ∧ count_paths Cg = ok rCg ∧ r.val = rCg.val) := by
    sorry

  /-- Let C(grid) be the actual number of strictly increasing paths (finite adjacent cell sequences with strictly increasing values, as in spec_1). The function returns a result r with r = C(grid) mod 1000000007, and C(grid) >= m*n + 1.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. Assume there exist adjacent cells (i,j) and (i',j') with |i-i'| + |j-j'| = 1 and grid[i][j] != grid[i'][j']. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
      (hwitness : ∃ (p q : Nat × Nat) (v w : Int),
        p.1 < m ∧ p.2 < n ∧ q.1 < m ∧ q.2 < n ∧ Adjacent p q ∧
          cellAt grid p.1 p.2 = some v ∧ cellAt grid q.1 q.2 = some w ∧ v ≠ w) :
      (∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((C grid % 1000000007 : Nat) : Int)) ∧
        m * n + 1 ≤ C grid := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n)
        (hwitness : ∃ (p q : Nat × Nat) (v w : Int),
          p.1 < m ∧ p.2 < n ∧ q.1 < m ∧ q.2 < n ∧ Adjacent p q ∧
            cellAt grid p.1 p.2 = some v ∧ cellAt grid q.1 q.2 = some w ∧ v ≠ w), (∃ r : Std.I64, count_paths grid = ok r ∧ r.val = ((C grid % 1000000007 : Nat) : Int)) ∧
          m * n + 1 ≤ C grid) := by
    sorry

  /-- Let M = 1000000007. For each cell (r,c) with 0 <= r < m and 0 <= c < n, let D(r,c) be the number of strictly increasing paths (as in spec_1) whose first cell is (r,c). Then D(r,c) = 1 + sum over all (r',c') with 0 <= r' < m, 0 <= c' < n, |r'-r| + |c'-c| = 1, and grid[r][c] < grid[r'][c'], of D(r',c'). Let C(grid) be the total number of strictly increasing paths as in spec_1; then C(grid) = sum over all cells (r,c) of D(r,c). The function returns a result r with r = C(grid) mod M.
    Preconditions: grid is a nonempty rectangular matrix (all rows have the same length n): m = len(grid), n = len(grid[0]), 1 <= m <= 1000, 1 <= n <= 1000, m*n <= 100000, and for every i with 0 <= i < m and every j with 0 <= j < n, 1 <= grid[i][j] <= 100000. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hrect : Rect grid m n)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
      (hmn : m * n ≤ 100000) (hval : ValRange grid m n) :
      (∀ r c : Nat, r < m → c < n →
        numIncPathsFrom (gridVals grid) m n (r, c) =
          1 + ∑ q ∈ betterNeighbours (gridVals grid) m n (r, c),
                numIncPathsFrom (gridVals grid) m n q) ∧
      (numIncPaths (gridVals grid) m n =
        ∑ p ∈ cellFinset m n, numIncPathsFrom (gridVals grid) m n p) ∧
      (∃ r : Std.I64, count_paths grid = ok r ∧
        r.val = ((numIncPaths (gridVals grid) m n % 1000000007 : Nat) : Int)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hrect : Rect grid m n)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 1000) (hn1 : 1 ≤ n) (hn2 : n ≤ 1000)
        (hmn : m * n ≤ 100000) (hval : ValRange grid m n), (∀ r c : Nat, r < m → c < n →
          numIncPathsFrom (gridVals grid) m n (r, c) =
            1 + ∑ q ∈ betterNeighbours (gridVals grid) m n (r, c),
                  numIncPathsFrom (gridVals grid) m n q) ∧
        (numIncPaths (gridVals grid) m n =
          ∑ p ∈ cellFinset m n, numIncPathsFrom (gridVals grid) m n p) ∧
        (∃ r : Std.I64, count_paths grid = ok r ∧
          r.val = ((numIncPaths (gridVals grid) m n % 1000000007 : Nat) : Int))) := by
    sorry

  end AegisSpec.CountPaths
