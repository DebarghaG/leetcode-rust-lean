import Aegis.MinScore.Code.Funs

/-!
# Specifications of `Aegis.MinScore.min_score`

LeetCode problem `minimize-maximum-value-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinScore

  def matOf (rows : List (alloc.vec.Vec Std.I64)) : List (List Int) :=
    rows.map (fun row => row.val.map (fun x => x.val))

  def gridMat (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    matOf grid.val

  def resMat (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List Int) :=
    matOf res.val

  def entry? (M : List (List Int)) (r c : Nat) : Option Int :=
    (M[r]?).bind (fun row => row[c]?)

  def entry (M : List (List Int)) (r c : Nat) : Int := (entry? M r c).getD 0

  def maxCell (M : List (List Int)) : Int := M.flatten.foldr max 0

  def HasShape (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    res.val.length = m ∧ ∀ r, r < m → ∃ row, res.val[r]? = some row ∧ row.val.length = n

  structure GridPre (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop where

    m_eq : grid.val.length = m

    m_pos : 1 ≤ m

    m_le : m ≤ 1000

    n_pos : 1 ≤ n

    n_le : n ≤ 1000

    cells_le : m * n ≤ 100000

    row_len : ∀ r, r < m → ∃ row, (gridMat grid)[r]? = some row ∧ row.length = n

    entry_bounds : ∀ r c v, entry? (gridMat grid) r c = some v → 1 ≤ v ∧ v ≤ 1000000000

    entry_distinct : ∀ r1 c1 r2 c2 v1 v2,
      entry? (gridMat grid) r1 c1 = some v1 → entry? (gridMat grid) r2 c2 = some v2 →
      (r1 ≠ r2 ∨ c1 ≠ c2) → v1 ≠ v2

  def IsPosMatrix (B : List (List Int)) (m n : Nat) : Prop :=
    B.length = m ∧ (∀ r, r < m → ∃ row, B[r]? = some row ∧ row.length = n) ∧
      ∀ r c, r < m → c < n → 1 ≤ entry B r c

  def PreservesOrder (G B : List (List Int)) (m n : Nat) : Prop :=
    (∀ r c1 c2, r < m → c1 < n → c2 < n →
        entry G r c1 > entry G r c2 → entry B r c1 > entry B r c2) ∧
      (∀ c r1 r2, c < n → r1 < m → r2 < m →
        entry G r1 c > entry G r2 c → entry B r1 c > entry B r2 c)

  def IsValid (G B : List (List Int)) (m n : Nat) : Prop :=
    IsPosMatrix B m n ∧ PreservesOrder G B m n

  def IsLeastBound (G : List (List Int)) (m n : Nat) (K : Int) : Prop :=
    1 ≤ K ∧
      (∃ B, IsValid G B m n ∧ ∀ r c, r < m → c < n → entry B r c ≤ K) ∧
      (∀ K' : Int, 1 ≤ K' →
        (∃ B, IsValid G B m n ∧ ∀ r c, r < m → c < n → entry B r c ≤ K') → K ≤ K')

  def IsChain (G : List (List Int)) : List (Nat × Nat) → Prop
    | [] => False
    | [_] => True
    | (r1, c1) :: (r2, c2) :: rest =>
      (r1 = r2 ∨ c1 = c2) ∧ entry G r1 c1 < entry G r2 c2 ∧
        IsChain G ((r2, c2) :: rest)

  def IsChainIn (G : List (List Int)) (m n : Nat) (cs : List (Nat × Nat)) : Prop :=
    (∀ p ∈ cs, p.1 < m ∧ p.2 < n) ∧ IsChain G cs

  def MaxChainLen (G : List (List Int)) (m n : Nat) (L : Nat) : Prop :=
    (∃ cs, IsChainIn G m n cs ∧ cs.length = L) ∧
      ∀ cs, IsChainIn G m n cs → cs.length ≤ L

  def EndsAt (cs : List (Nat × Nat)) (r c : Nat) : Prop := cs.getLast? = some (r, c)

  def StartsAt (cs : List (Nat × Nat)) (r c : Nat) : Prop := cs.head? = some (r, c)

  def MaxEndLen (G : List (List Int)) (m n r c : Nat) (L : Nat) : Prop :=
    (∃ cs, IsChainIn G m n cs ∧ EndsAt cs r c ∧ cs.length = L) ∧
      ∀ cs, IsChainIn G m n cs → EndsAt cs r c → cs.length ≤ L

  def MaxStartLen (G : List (List Int)) (m n r c : Nat) (L : Nat) : Prop :=
    (∃ cs, IsChainIn G m n cs ∧ StartsAt cs r c ∧ cs.length = L) ∧
      ∀ cs, IsChainIn G m n cs → StartsAt cs r c → cs.length ≤ L

  def countSmallerInRow (G : List (List Int)) (n r c : Nat) : Nat :=
    ((List.range n).filter (fun c' => decide (entry G r c' < entry G r c))).length

  def countSmallerInCol (G : List (List Int)) (m r c : Nat) : Nat :=
    ((List.range m).filter (fun r' => decide (entry G r' c < entry G r c))).length

  /-- `min_score grid` returns a result `res`. Call an m-by-n matrix B of positive integers valid if for every row r and columns c1,c2, grid[r][c1] > grid[r][c2] implies B[r][c1] > B[r][c2], and for every column c and rows r1,r2, grid[r1][c] > grid[r2][c] implies B[r1][c] > B[r2][c]. Let K be the least positive integer such that some valid B satisfies B[r][c] <= K for every cell. Then res is valid, so it has shape m-by-n and positive entries, and max over all cells of res equals K.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct: for any two distinct cells (r,c) and (r',c'), grid[r][c] != grid[r'][c']. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        IsValid (gridMat grid) (resMat res) m n ∧
          ∃ K : Int, IsLeastBound (gridMat grid) m n K ∧ maxCell (resMat res) = K := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          IsValid (gridMat grid) (resMat res) m n ∧
            ∃ K : Int, IsLeastBound (gridMat grid) m n K ∧ maxCell (resMat res) = K) := by
    sorry

  /-- `min_score grid` returns a result `res`; in particular it does not fail, panic, or overflow.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n) :
      ∃ res, Aegis.MinScore.min_score grid = ok res := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n), ∃ res, Aegis.MinScore.min_score grid = ok res) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, len(res) = m and for every r with 0 <= r < m, len(res[r]) = n.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res → HasShape res m n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res → HasShape res m n) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, for every r,c with 0 <= r < m and 0 <= c < n, res[r][c] > 0.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ r c, r < m → c < n → 0 < entry (resMat res) r c := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ r c, r < m → c < n → 0 < entry (resMat res) r c) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, for every row r and columns c1,c2 with 0 <= r < m, 0 <= c1 < n, and 0 <= c2 < n, if grid[r][c1] > grid[r][c2] then res[r][c1] > res[r][c2].
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ r c1 c2, r < m → c1 < n → c2 < n →
          entry (gridMat grid) r c1 > entry (gridMat grid) r c2 →
            entry (resMat res) r c1 > entry (resMat res) r c2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ r c1 c2, r < m → c1 < n → c2 < n →
            entry (gridMat grid) r c1 > entry (gridMat grid) r c2 →
              entry (resMat res) r c1 > entry (resMat res) r c2) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, for every column c and rows r1,r2 with 0 <= c < n, 0 <= r1 < m, and 0 <= r2 < m, if grid[r1][c] > grid[r2][c] then res[r1][c] > res[r2][c].
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ c r1 r2, c < n → r1 < m → r2 < m →
          entry (gridMat grid) r1 c > entry (gridMat grid) r2 c →
            entry (resMat res) r1 c > entry (resMat res) r2 c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ c r1 r2, c < n → r1 < m → r2 < m →
            entry (gridMat grid) r1 c > entry (gridMat grid) r2 c →
              entry (resMat res) r1 c > entry (resMat res) r2 c) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, for every m-by-n matrix B of positive integers that preserves the strict relative order of every two cells lying in the same row or the same column of grid, max over all cells of res is <= max over all cells of B.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ B : List (List Int), IsValid (gridMat grid) B m n →
          maxCell (resMat res) ≤ maxCell B := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ B : List (List Int), IsValid (gridMat grid) B m n →
            maxCell (resMat res) ≤ maxCell B) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, max over all cells of res is <= m*n.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        maxCell (resMat res) ≤ ((m * n : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          maxCell (resMat res) ≤ ((m * n : Nat) : Int)) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, max over all cells of res is >= max(m,n).
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ((Nat.max m n : Nat) : Int) ≤ maxCell (resMat res) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ((Nat.max m n : Nat) : Int) ≤ maxCell (resMat res)) := by
    sorry

  /-- A same-row-or-column increasing chain is a nonempty finite sequence of cells (r_0,c_0),...,(r_{k-1},c_{k-1}) in the grid such that for each i with 0 <= i < k-1, either r_i = r_{i+1} or c_i = c_{i+1}, and grid[r_i][c_i] < grid[r_{i+1}][c_{i+1}]. Let L be the maximum length k of such a chain. Whenever `min_score grid` returns a result `res`, max over all cells of res equals L.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ L : Nat, MaxChainLen (gridMat grid) m n L →
          maxCell (resMat res) = (L : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ L : Nat, MaxChainLen (gridMat grid) m n L →
            maxCell (resMat res) = (L : Int)) := by
    sorry

  /-- For a cell (r,c), let L_end(r,c) be the maximum length of a same-row-or-column increasing chain ending at (r,c), where a chain is a sequence of cells (r_0,c_0),...,(r_{k-1},c_{k-1}) such that (r_{k-1},c_{k-1}) = (r,c), for each i with 0 <= i < k-1 either r_i = r_{i+1} or c_i = c_{i+1}, and grid[r_i][c_i] < grid[r_{i+1}][c_{i+1}]. Whenever `min_score grid` returns a result `res`, for every cell (r,c), res[r][c] >= L_end(r,c).
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ r c L, r < m → c < n → MaxEndLen (gridMat grid) m n r c L →
          (L : Int) ≤ entry (resMat res) r c := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ r c L, r < m → c < n → MaxEndLen (gridMat grid) m n r c L →
            (L : Int) ≤ entry (resMat res) r c) := by
    sorry

  /-- For a cell (r,c), let U_start(r,c) be the maximum length of a same-row-or-column increasing chain starting at (r,c), where a chain is a sequence of cells (r_0,c_0),...,(r_{k-1},c_{k-1}) such that (r_0,c_0) = (r,c), for each i with 0 <= i < k-1 either r_i = r_{i+1} or c_i = c_{i+1}, and grid[r_i][c_i] < grid[r_{i+1}][c_{i+1}]. Whenever `min_score grid` returns a result `res`, for every cell (r,c), res[r][c] + U_start(r,c) - 1 <= max over all cells of res.
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        ∀ r c U, r < m → c < n → MaxStartLen (gridMat grid) m n r c U →
          entry (resMat res) r c + (U : Int) - 1 ≤ maxCell (resMat res) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          ∀ r c U, r < m → c < n → MaxStartLen (gridMat grid) m n r c U →
            entry (resMat res) r c + (U : Int) - 1 ≤ maxCell (resMat res)) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, len(res) = 1, len(res[0]) = n, and for every c with 0 <= c < n, res[0][c] = 1 + the number of columns c' with 0 <= c' < n and grid[0][c'] < grid[0][c].
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. In addition, m = 1. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (hm : m = 1) (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        HasShape res 1 n ∧
          ∀ c, c < n →
            entry (resMat res) 0 c = 1 + (countSmallerInRow (gridMat grid) n 0 c : Int) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (hm : m = 1) (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          HasShape res 1 n ∧
            ∀ c, c < n →
              entry (resMat res) 0 c = 1 + (countSmallerInRow (gridMat grid) n 0 c : Int)) := by
    sorry

  /-- Whenever `min_score grid` returns a result `res`, len(res) = m, for every r with 0 <= r < m len(res[r]) = 1, and for every r with 0 <= r < m, res[r][0] = 1 + the number of rows r' with 0 <= r' < m and grid[r'][0] < grid[r][0].
    Preconditions: Let m = len(grid). The slice grid is nonempty, so m >= 1. Let n = len(grid[0]). Every row grid[r] with 0 <= r < m has length n, with 1 <= m <= 1000, 1 <= n <= 1000, and m*n <= 100000. For every r,c with 0 <= r < m and 0 <= c < n, 1 <= grid[r][c] <= 1000000000. All entries of grid are pairwise distinct. In addition, n = 1. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
      (hn : n = 1) (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)) :
      Aegis.MinScore.min_score grid = ok res →
        HasShape res m 1 ∧
          ∀ r, r < m →
            entry (resMat res) r 0 = 1 + (countSmallerInCol (gridMat grid) m r 0 : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (hpre : GridPre grid m n)
        (hn : n = 1) (res : alloc.vec.Vec (alloc.vec.Vec Std.I64)), Aegis.MinScore.min_score grid = ok res →
          HasShape res m 1 ∧
            ∀ r, r < m →
              entry (resMat res) r 0 = 1 + (countSmallerInCol (gridMat grid) m r 0 : Int)) := by
    sorry

  end AegisSpec.MinScore
