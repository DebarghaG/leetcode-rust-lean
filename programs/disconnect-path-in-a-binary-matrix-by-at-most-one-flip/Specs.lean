import Aegis.IsPossibleToCutPath.Code.Funs

/-!
# Specifications of `Aegis.IsPossibleToCutPath.is_possible_to_cut_path`

LeetCode problem `disconnect-path-in-a-binary-matrix-by-at-most-one-flip`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsPossibleToCutPath

  def rows (grid : Slice (alloc.vec.Vec Std.I64)) : List (List Std.I64) :=
    grid.val.map (fun row => row.val)

  def row (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List Std.I64 :=
    (rows grid).getD i []

  def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    match (row grid i)[j]? with
    | none => 0
    | some x => x.val

  def mat (grid : Slice (alloc.vec.Vec Std.I64)) : Nat → Nat → Int :=
    fun i j => entry grid i j

  def consec : List α → List (α × α)
    | [] => []
    | [_] => []
    | a :: b :: l => (a, b) :: consec (b :: l)

  def IsDRPath (X : Nat → Nat → Int) (m n : Nat) (p : List (Nat × Nat)) : Prop :=
    p.head? = some (0, 0) ∧
    p.getLast? = some (m - 1, n - 1) ∧
    (∀ c ∈ p, c.1 < m ∧ c.2 < n ∧ X c.1 c.2 = 1) ∧
    (∀ q ∈ consec p, q.2 = (q.1.1 + 1, q.1.2) ∨ q.2 = (q.1.1, q.1.2 + 1))

  def HasDRPath (X : Nat → Nat → Int) (m n : Nat) : Prop :=
    ∃ p, IsDRPath X m n p

  def flipAt (X : Nat → Nat → Int) (i j : Nat) : Nat → Nat → Int :=
    fun a b => if a = i ∧ b = j then 1 - X a b else X a b

  def InternallyDisjoint (m n : Nat) (p q : List (Nat × Nat)) : Prop :=
    ∀ c, c ∈ p → c ∈ q → c = (0, 0) ∨ c = (m - 1, n - 1)

  /-- Whenever is_possible_to_cut_path(grid) returns a Boolean r, r = true if and only if there exists an m-by-n matrix H such that: either H = grid, or H is obtained from grid by changing exactly one cell (i,j) with 0 <= i < m, 0 <= j < n, (i,j) != (0,0), (i,j) != (m-1,n-1), by setting H[i][j] = 1 - grid[i][j] and H[a][b] = grid[a][b] for all other cells; and H has no down/right 1-path from (0,0) to (m-1,n-1).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input grid is a nonempty rectangular matrix: every row of grid has length n, 1 <= m, 1 <= n, and m*n <= 100000. Every entry grid[i][j] is 0 or 1. Also grid[0][0] = 1 and grid[m-1][n-1] = 1. A down/right 1-path in an m-by-n matrix X is a finite sequence ((r_0,c_0),...,(r_k,c_k)) such that (r_0,c_0) = (0,0), (r_k,c_k) = (m-1,n-1), for each t < k either (r_{t+1},c_{t+1}) = (r_t+1,c_t) or (r_{t+1},c_{t+1}) = (r_t,c_t+1), and X[r_t][c_t] = 1 for every t. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1) :
      ∃ r : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
        (r = true ↔
          ∃ H : Nat → Nat → Int,
            (H = mat grid ∨
              ∃ i j : Nat,
                i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
                  H = flipAt (mat grid) i j) ∧
            ¬ HasDRPath H m n) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1), ∃ r : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
          (r = true ↔
            ∃ H : Nat → Nat → Int,
              (H = mat grid ∨
                ∃ i j : Nat,
                  i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
                    H = flipAt (mat grid) i j) ∧
              ¬ HasDRPath H m n)) := by
    sorry

  /-- The call is_possible_to_cut_path(grid) does not fail: it returns some Boolean result, with no overflow, out-of-bounds indexing, or panic, for every input satisfying the preconditions.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1) :
      ∃ r : Bool, Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1), ∃ r : Bool, Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r) := by
    sorry

  /-- The function returns true if and only if there exists a cell (i,j) with 0 <= i < m, 0 <= j < n, (i,j) != (0,0), (i,j) != (m-1,n-1), and grid[i][j] = 1, such that the matrix H with H[i][j] = 0 and H[a][b] = grid[a][b] for all (a,b) != (i,j) has no down/right 1-path from (0,0) to (m-1,n-1).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. A down/right 1-path is a sequence of cells from (0,0) to (m-1,n-1) whose steps are only to (r+1,c) or (r,c+1) and whose every visited cell has value 1. Additionally, grid itself has a down/right 1-path from (0,0) to (m-1,n-1). -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (hpath : HasDRPath (mat grid) m n) :
      ∃ r : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
        (r = true ↔
          ∃ i j : Nat,
            i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
              entry grid i j = 1 ∧ ¬ HasDRPath (flipAt (mat grid) i j) m n) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (hpath : HasDRPath (mat grid) m n), ∃ r : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
          (r = true ↔
            ∃ i j : Nat,
              i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
                entry grid i j = 1 ∧ ¬ HasDRPath (flipAt (mat grid) i j) m n)) := by
    sorry

  /-- Whenever is_possible_to_cut_path(grid) returns false, the original grid has a down/right 1-path from (0,0) to (m-1,n-1); equivalently, if the original matrix is disconnected, the function cannot return false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. A down/right 1-path is a sequence of cells from (0,0) to (m-1,n-1) whose steps are only to (r+1,c) or (r,c+1) and whose every visited cell has value 1. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false →
        HasDRPath (mat grid) m n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1), Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false →
          HasDRPath (mat grid) m n) := by
    sorry

  /-- Whenever is_possible_to_cut_path(grid) returns false, for every cell (i,j) with 0 <= i < m, 0 <= j < n, (i,j) != (0,0), (i,j) != (m-1,n-1), the matrix obtained from grid by setting that cell to 1 - grid[i][j] and leaving all other cells unchanged still has a down/right 1-path from (0,0) to (m-1,n-1).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. A down/right 1-path is a sequence of cells from (0,0) to (m-1,n-1) whose steps are only to (r+1,c) or (r,c+1) and whose every visited cell has value 1. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false →
        ∀ i j : Nat,
          i < m → j < n → (i ≠ 0 ∨ j ≠ 0) → (i ≠ m - 1 ∨ j ≠ n - 1) →
            HasDRPath (flipAt (mat grid) i j) m n := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1), Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false →
          ∀ i j : Nat,
            i < m → j < n → (i ≠ 0 ∨ j ≠ 0) → (i ≠ m - 1 ∨ j ≠ n - 1) →
              HasDRPath (flipAt (mat grid) i j) m n) := by
    sorry

  /-- Whenever is_possible_to_cut_path(grid) returns true, there exists a cell (i,j) with 0 <= i < m, 0 <= j < n, (i,j) != (0,0), (i,j) != (m-1,n-1), and grid[i][j] = 1 such that every down/right 1-path from (0,0) to (m-1,n-1) in grid contains the cell (i,j).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. A down/right 1-path is a sequence of cells from (0,0) to (m-1,n-1) whose steps are only to (r+1,c) or (r,c+1) and whose every visited cell has value 1. Additionally, grid itself has a down/right 1-path from (0,0) to (m-1,n-1). -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (hpath : HasDRPath (mat grid) m n) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok true →
        ∃ i j : Nat,
          i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
            entry grid i j = 1 ∧
            (∀ p, IsDRPath (mat grid) m n p → (i, j) ∈ p) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (hpath : HasDRPath (mat grid) m n), Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok true →
          ∃ i j : Nat,
            i < m ∧ j < n ∧ (i ≠ 0 ∨ j ≠ 0) ∧ (i ≠ m - 1 ∨ j ≠ n - 1) ∧
              entry grid i j = 1 ∧
              (∀ p, IsDRPath (mat grid) m n p → (i, j) ∈ p)) := by
    sorry

  /-- The function returns false.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. Additionally, m*n <= 2. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (hsmall : m * n ≤ 2) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (hsmall : m * n ≤ 2), Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok false) := by
    sorry

  /-- The function returns true.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. Additionally, either (m = 1 and n >= 3) or (n = 1 and m >= 3). -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (hline : (m = 1 ∧ 3 ≤ n) ∨ (n = 1 ∧ 3 ≤ m)) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok true := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (hline : (m = 1 ∧ 3 ≤ n) ∨ (n = 1 ∧ 3 ≤ m)), Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok true) := by
    sorry

  /-- The function returns true if and only if grid[0][1] = 0 or grid[1][0] = 0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, m = 2, n = 2, every entry is 0 or 1, and grid[0][0] = grid[1][1] = 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : m = 2) (hn : n = 2)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1) :
      ∃ r : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
        (r = true ↔ entry grid 0 1 = 0 ∨ entry grid 1 0 = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : m = 2) (hn : n = 2)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1), ∃ r : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
          (r = true ↔ entry grid 0 1 = 0 ∨ entry grid 1 0 = 0)) := by
    sorry

  /-- Let T be the n-by-m transpose matrix defined by T[j][i] = grid[i][j] for 0 <= i < m and 0 <= j < n. Then is_possible_to_cut_path(grid) returns the same Boolean value as is_possible_to_cut_path(T).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (T : Slice (alloc.vec.Vec Std.I64))
      (hTlen : (T.val).length = n)
      (hTrows : ∀ j, j < n → (row T j).length = m)
      (hT : ∀ i j, i < m → j < n → entry T j i = entry grid i j) :
      ∀ rg rT : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok rg →
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path T = ok rT → rg = rT := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (T : Slice (alloc.vec.Vec Std.I64))
        (hTlen : (T.val).length = n)
        (hTrows : ∀ j, j < n → (row T j).length = m)
        (hT : ∀ i j, i < m → j < n → entry T j i = entry grid i j), ∀ rg rT : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok rg →
            Aegis.IsPossibleToCutPath.is_possible_to_cut_path T = ok rT → rg = rT) := by
    sorry

  /-- Let R be the m-by-n matrix defined by R[i][j] = grid[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. Then is_possible_to_cut_path(grid) returns the same Boolean value as is_possible_to_cut_path(R).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (R : Slice (alloc.vec.Vec Std.I64))
      (hRlen : (R.val).length = m)
      (hRrows : ∀ i, i < m → (row R i).length = n)
      (hR : ∀ i j, i < m → j < n → entry R i j = entry grid (m - 1 - i) (n - 1 - j)) :
      ∀ rg rR : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok rg →
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path R = ok rR → rg = rR := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (R : Slice (alloc.vec.Vec Std.I64))
        (hRlen : (R.val).length = m)
        (hRrows : ∀ i, i < m → (row R i).length = n)
        (hR : ∀ i j, i < m → j < n → entry R i j = entry grid (m - 1 - i) (n - 1 - j)), ∀ rg rR : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok rg →
            Aegis.IsPossibleToCutPath.is_possible_to_cut_path R = ok rR → rg = rR) := by
    sorry

  /-- Whenever is_possible_to_cut_path(G) returns true, is_possible_to_cut_path(G') also returns true.
    Preconditions: Let G and G' be two matrices satisfying all of the input preconditions with the same dimensions m-by-n, where m = len(G), n = len(G[0]), every row has length n, 1 <= m, 1 <= n, m*n <= 100000, all entries are 0 or 1, and G[0][0] = G[m-1][n-1] = G'[0][0] = G'[m-1][n-1] = 1. Suppose G'[i][j] <= G[i][j] for every 0 <= i < m and 0 <= j < n, so G' is obtained from G by changing some non-endpoint 1-cells to 0. -/
  theorem spec_12 (G G' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (G.val).length = m)
      (hrows : ∀ i, i < m → (row G i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry G i j = 0 ∨ entry G i j = 1)
      (hstart : entry G 0 0 = 1) (hend : entry G (m - 1) (n - 1) = 1)
      (hlen' : (G'.val).length = m)
      (hrows' : ∀ i, i < m → (row G' i).length = n)
      (hbin' : ∀ i j, i < m → j < n → entry G' i j = 0 ∨ entry G' i j = 1)
      (hstart' : entry G' 0 0 = 1) (hend' : entry G' (m - 1) (n - 1) = 1)
      (hle : ∀ i j, i < m → j < n → entry G' i j ≤ entry G i j) :
      Aegis.IsPossibleToCutPath.is_possible_to_cut_path G = ok true →
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path G' = ok true := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (G G' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (G.val).length = m)
        (hrows : ∀ i, i < m → (row G i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry G i j = 0 ∨ entry G i j = 1)
        (hstart : entry G 0 0 = 1) (hend : entry G (m - 1) (n - 1) = 1)
        (hlen' : (G'.val).length = m)
        (hrows' : ∀ i, i < m → (row G' i).length = n)
        (hbin' : ∀ i j, i < m → j < n → entry G' i j = 0 ∨ entry G' i j = 1)
        (hstart' : entry G' 0 0 = 1) (hend' : entry G' (m - 1) (n - 1) = 1)
        (hle : ∀ i j, i < m → j < n → entry G' i j ≤ entry G i j), Aegis.IsPossibleToCutPath.is_possible_to_cut_path G = ok true →
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path G' = ok true) := by
    sorry

  /-- The function returns false if and only if there exist two down/right 1-paths in grid from (0,0) to (m-1,n-1) that are internally vertex-disjoint.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Every row of grid has length n, 1 <= m, 1 <= n, m*n <= 100000, every entry is 0 or 1, and grid[0][0] = grid[m-1][n-1] = 1. A down/right 1-path is a sequence of cells from (0,0) to (m-1,n-1) whose steps are only to (r+1,c) or (r,c+1) and whose every visited cell has value 1. Additionally, grid itself has a down/right 1-path from (0,0) to (m-1,n-1) and m*n >= 3. Two down/right 1-paths are internally vertex-disjoint if they have no cell in common except (0,0) and (m-1,n-1). -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hlen : (grid.val).length = m)
      (hrows : ∀ i, i < m → (row grid i).length = n)
      (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
      (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
      (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
      (hpath : HasDRPath (mat grid) m n) (hbig : 3 ≤ m * n) :
      ∃ r : Bool,
        Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
        (r = false ↔
          ∃ p q : List (Nat × Nat),
            IsDRPath (mat grid) m n p ∧ IsDRPath (mat grid) m n q ∧
              InternallyDisjoint m n p q) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hlen : (grid.val).length = m)
        (hrows : ∀ i, i < m → (row grid i).length = n)
        (hm : 1 ≤ m) (hn : 1 ≤ n) (hsize : m * n ≤ 100000)
        (hbin : ∀ i j, i < m → j < n → entry grid i j = 0 ∨ entry grid i j = 1)
        (hstart : entry grid 0 0 = 1) (hend : entry grid (m - 1) (n - 1) = 1)
        (hpath : HasDRPath (mat grid) m n) (hbig : 3 ≤ m * n), ∃ r : Bool,
          Aegis.IsPossibleToCutPath.is_possible_to_cut_path grid = ok r ∧
          (r = false ↔
            ∃ p q : List (Nat × Nat),
              IsDRPath (mat grid) m n p ∧ IsDRPath (mat grid) m n q ∧
                InternallyDisjoint m n p q)) := by
    sorry

  end AegisSpec.IsPossibleToCutPath
