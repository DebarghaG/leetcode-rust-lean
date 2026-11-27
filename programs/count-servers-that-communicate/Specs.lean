import Aegis.CountServers.Code.Funs

/-!
# Specifications of `Aegis.CountServers.count_servers`

LeetCode problem `count-servers-that-communicate`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountServers

  namespace AegisSpec.CountServers

  def numRows (grid : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    grid.val.length

  def rowLen (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    match grid.val[i]? with
    | none => 0
    | some row => row.val.length

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    match grid.val[i]? with
    | none => 0
    | some row =>
      match row.val[j]? with
      | none => 0
      | some x => x.val

  def IsBinaryMatrix (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
    1 ≤ m ∧ m ≤ 250 ∧ 1 ≤ n ∧ n ≤ 250 ∧
      numRows grid = m ∧
      (∀ i, i < m → rowLen grid i = n) ∧
      (∀ i j, i < m → j < n → cell grid i j = 0 ∨ cell grid i j = 1)

  def rowOnes (grid : Slice (alloc.vec.Vec Std.I64)) (n i : ℕ) : ℕ :=
    ((Finset.range n).filter (fun j => cell grid i j = 1)).card

  def colOnes (grid : Slice (alloc.vec.Vec Std.I64)) (m j : ℕ) : ℕ :=
    ((Finset.range m).filter (fun i => cell grid i j = 1)).card

  def totalOnes (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    (((Finset.range m).product (Finset.range n)).filter
      (fun p : ℕ × ℕ => cell grid p.1 p.2 = 1)).card

  def serverCells (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    (((Finset.range m).product (Finset.range n)).filter
      (fun p : ℕ × ℕ =>
        cell grid p.1 p.2 = 1 ∧ (2 ≤ rowOnes grid n p.1 ∨ 2 ≤ colOnes grid m p.2))).card

  def rowServerCells (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℕ :=
    (((Finset.range m).product (Finset.range n)).filter
      (fun p : ℕ × ℕ => cell grid p.1 p.2 = 1 ∧ 2 ≤ rowOnes grid n p.1)).card

  def permuteRow {m : ℕ} (π : Equiv.Perm (Fin m)) (i : ℕ) : ℕ :=
    if h : i < m then ((π ⟨i, h⟩ : Fin m) : ℕ) else i

  def permuteCol {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : ℕ) : ℕ :=
    if h : j < n then ((σ ⟨j, h⟩ : Fin n) : ℕ) else j

  def IsTranspose (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
    numRows gridT = n ∧
      (∀ j, j < n → rowLen gridT j = m) ∧
      (∀ i j, i < m → j < n → cell gridT j i = cell grid i j)

  def IsRowPerm (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (π : Equiv.Perm (Fin m)) : Prop :=
    numRows grid' = m ∧
      (∀ i, i < m → rowLen grid' i = n) ∧
      (∀ i j, i < m → j < n → cell grid' i j = cell grid (permuteRow π i) j)

  def IsColPerm (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (σ : Equiv.Perm (Fin n)) : Prop :=
    numRows grid' = m ∧
      (∀ i, i < m → rowLen grid' i = n) ∧
      (∀ i j, i < m → j < n → cell grid' i j = cell grid i (permuteCol σ j))

  /-- Let m = len(grid) and n = len(grid[0]). For each i with 0 <= i < m, let rowOnes(i) be the number of j with 0 <= j < n and grid[i][j] = 1. For each j with 0 <= j < n, let colOnes(j) be the number of i with 0 <= i < m and grid[i][j] = 1. The function returns a result r and r is exactly the number of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = 1, and (rowOnes(i) >= 2 or colOnes(j) >= 2).
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ r.val = (serverCells grid m n : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧ r.val = (serverCells grid m n : ℤ)) := by
    sorry

  /-- For every grid satisfying the preconditions, the function returns some result r; it does not fail.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r) := by
    sorry

  /-- The function returns a result r and r >= 0.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧ 0 ≤ r.val) := by
    sorry

  /-- Let S be the number of pairs (i,j) with 0 <= i < len(grid), 0 <= j < len(grid[0]), and grid[i][j] = 1. The function returns a result r and r <= S.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ r.val ≤ (totalOnes grid m n : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧ r.val ≤ (totalOnes grid m n : ℤ)) := by
    sorry

  /-- The function returns a result r and r != 1; equivalently, r = 0 or r >= 2.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ r.val ≠ 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧ r.val ≠ 1) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). For each i with 0 <= i < m, let rowOnes(i) be the number of j with 0 <= j < n and grid[i][j] = 1. For each j with 0 <= j < n, let colOnes(j) be the number of i with 0 <= i < m and grid[i][j] = 1. The function returns a result r and r = 0 if and only if for every i,j with 0 <= i < m, 0 <= j < n, and grid[i][j] = 1, we have rowOnes(i) = 1 and colOnes(j) = 1.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧
        (r.val = 0 ↔
          ∀ i j, i < m → j < n → cell grid i j = 1 →
            rowOnes grid n i = 1 ∧ colOnes grid m j = 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧
          (r.val = 0 ↔
            ∀ i j, i < m → j < n → cell grid i j = 1 →
              rowOnes grid n i = 1 ∧ colOnes grid m j = 1)) := by
    sorry

  /-- Let n = len(grid[0]) and let S be the number of j with 0 <= j < n and grid[0][j] = 1. The function returns a result r and r = S if S >= 2, and r = 0 if S <= 1.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n; and len(grid) = 1. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (hm : m = 1) :
      ∃ r : Std.I64, count_servers grid = ok r ∧
        (2 ≤ rowOnes grid n 0 → r.val = (rowOnes grid n 0 : ℤ)) ∧
        (rowOnes grid n 0 ≤ 1 → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (hm : m = 1), ∃ r : Std.I64, count_servers grid = ok r ∧
          (2 ≤ rowOnes grid n 0 → r.val = (rowOnes grid n 0 : ℤ)) ∧
          (rowOnes grid n 0 ≤ 1 → r.val = 0)) := by
    sorry

  /-- Let m = len(grid) and let S be the number of i with 0 <= i < m and grid[i][0] = 1. The function returns a result r and r = S if S >= 2, and r = 0 if S <= 1.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n; and len(grid[0]) = 1. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (hn : n = 1) :
      ∃ r : Std.I64, count_servers grid = ok r ∧
        (2 ≤ colOnes grid m 0 → r.val = (colOnes grid m 0 : ℤ)) ∧
        (colOnes grid m 0 ≤ 1 → r.val = 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (hn : n = 1), ∃ r : Std.I64, count_servers grid = ok r ∧
          (2 ≤ colOnes grid m 0 → r.val = (colOnes grid m 0 : ℤ)) ∧
          (colOnes grid m 0 ≤ 1 → r.val = 0)) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). The function returns a result r and r = m*n if m*n >= 2; if m = n = 1 then r = 0.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n; and grid[i][j] = 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n)
      (hall : ∀ i j, i < m → j < n → cell grid i j = 1) :
      ∃ r : Std.I64, count_servers grid = ok r ∧
        (2 ≤ m * n → r.val = ((m * n : ℕ) : ℤ)) ∧
        (m = 1 → n = 1 → r.val = 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n)
        (hall : ∀ i j, i < m → j < n → cell grid i j = 1), ∃ r : Std.I64, count_servers grid = ok r ∧
          (2 ≤ m * n → r.val = ((m * n : ℕ) : ℤ)) ∧
          (m = 1 → n = 1 → r.val = 0)) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). For each i with 0 <= i < m, let rowOnes(i) be the number of j with 0 <= j < n and grid[i][j] = 1. Suppose that rowOnes(i) != 1 for every i with 0 <= i < m. Let S be the total number of server cells. The function returns a result r and r = S.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n)
      (hrows : ∀ i, i < m → rowOnes grid n i ≠ 1) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ r.val = (totalOnes grid m n : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n)
        (hrows : ∀ i, i < m → rowOnes grid n i ≠ 1), ∃ r : Std.I64, count_servers grid = ok r ∧ r.val = (totalOnes grid m n : ℤ)) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). For each i with 0 <= i < m, let rowOnes(i) be the number of j with 0 <= j < n and grid[i][j] = 1. Let T be the number of pairs (i,j) such that 0 <= i < m, 0 <= j < n, grid[i][j] = 1, and rowOnes(i) >= 2. The function returns a result r and r >= T.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) :
      ∃ r : Std.I64, count_servers grid = ok r ∧ (rowServerCells grid m n : ℤ) ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n), ∃ r : Std.I64, count_servers grid = ok r ∧ (rowServerCells grid m n : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever count_servers(g) returns r_g and count_servers(h) returns r_h, we have r_g <= r_h.
    Preconditions: g and h are nonempty rectangular 0/1 matrices with the same dimensions m and n; 1 <= m <= 250; 1 <= n <= 250; g[i][j] and h[i][j] are each 0 or 1 for every 0 <= i < m and 0 <= j < n; and g[i][j] <= h[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (g h : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hg : IsBinaryMatrix g m n) (hh : IsBinaryMatrix h m n)
      (hle : ∀ i j, i < m → j < n → cell g i j ≤ cell h i j)
      (rg rh : Std.I64) (hrg : count_servers g = ok rg) (hrh : count_servers h = ok rh) :
      rg.val ≤ rh.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (g h : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hg : IsBinaryMatrix g m n) (hh : IsBinaryMatrix h m n)
        (hle : ∀ i j, i < m → j < n → cell g i j ≤ cell h i j)
        (rg rh : Std.I64) (hrg : count_servers g = ok rg) (hrh : count_servers h = ok rh), rg.val ≤ rh.val) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]), and define the transpose matrix grid^T by len(grid^T) = n, len(grid^T[j]) = m for 0 <= j < n, and grid^T[j][i] = grid[i][j] for all i,j. Whenever count_servers(grid) returns r and count_servers(grid^T) returns r^T, we have r = r^T.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_13 (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (hT : IsBinaryMatrix gridT n m)
      (htr : IsTranspose grid gridT m n)
      (r rT : Std.I64) (hr : count_servers grid = ok r)
      (hrT : count_servers gridT = ok rT) :
      r.val = rT.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (hT : IsBinaryMatrix gridT n m)
        (htr : IsTranspose grid gridT m n)
        (r rT : Std.I64) (hr : count_servers grid = ok r)
        (hrT : count_servers gridT = ok rT), r.val = rT.val) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). For any permutation pi of the set {0,1,...,m-1}, define grid' by grid'[i][j] = grid[pi(i)][j] for 0 <= i < m and 0 <= j < n. Whenever count_servers(grid) returns r and count_servers(grid') returns r', we have r = r'.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_14 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (h' : IsBinaryMatrix grid' m n)
      (π : Equiv.Perm (Fin m)) (hperm : IsRowPerm grid grid' m n π)
      (r r' : Std.I64) (hr : count_servers grid = ok r)
      (hr' : count_servers grid' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (h' : IsBinaryMatrix grid' m n)
        (π : Equiv.Perm (Fin m)) (hperm : IsRowPerm grid grid' m n π)
        (r r' : Std.I64) (hr : count_servers grid = ok r)
        (hr' : count_servers grid' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let m = len(grid) and n = len(grid[0]). For any permutation sigma of the set {0,1,...,n-1}, define grid' by grid'[i][j] = grid[i][sigma(j)] for 0 <= i < m and 0 <= j < n. Whenever count_servers(grid) returns r and count_servers(grid') returns r', we have r = r'.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); and grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n. -/
  theorem spec_15 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (h' : IsBinaryMatrix grid' m n)
      (σ : Equiv.Perm (Fin n)) (hperm : IsColPerm grid grid' m n σ)
      (r r' : Std.I64) (hr : count_servers grid = ok r)
      (hr' : count_servers grid' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (h' : IsBinaryMatrix grid' m n)
        (σ : Equiv.Perm (Fin n)) (hperm : IsColPerm grid grid' m n σ)
        (r r' : Std.I64) (hr : count_servers grid = ok r)
        (hr' : count_servers grid' = ok r'), r.val = r'.val) := by
    sorry

  /-- Let the two server cells be (i1,j1) and (i2,j2). The function returns a result r and r = 2 if i1 = i2 or j1 = j2, and r = 0 otherwise.
    Preconditions: grid is a nonempty rectangular 0/1 matrix: 1 <= len(grid) <= 250; there exists an integer n with 1 <= n <= 250 such that len(grid[i]) = n for every i with 0 <= i < len(grid); grid[i][j] is either 0 or 1 for every 0 <= i < len(grid) and 0 <= j < n; and there are exactly two pairs (i,j) with grid[i][j] = 1. -/
  theorem spec_16 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : IsBinaryMatrix grid m n) (htwo : totalOnes grid m n = 2)
      (i1 j1 i2 j2 : ℕ) (hi1 : i1 < m) (hj1 : j1 < n) (hi2 : i2 < m) (hj2 : j2 < n)
      (hc1 : cell grid i1 j1 = 1) (hc2 : cell grid i2 j2 = 1)
      (hne : i1 ≠ i2 ∨ j1 ≠ j2)
      (honly : ∀ i j, i < m → j < n → cell grid i j = 1 →
        (i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2)) :
      ∃ r : Std.I64, count_servers grid = ok r ∧
        r.val = (if i1 = i2 ∨ j1 = j2 then (2 : ℤ) else 0) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : IsBinaryMatrix grid m n) (htwo : totalOnes grid m n = 2)
        (i1 j1 i2 j2 : ℕ) (hi1 : i1 < m) (hj1 : j1 < n) (hi2 : i2 < m) (hj2 : j2 < n)
        (hc1 : cell grid i1 j1 = 1) (hc2 : cell grid i2 j2 = 1)
        (hne : i1 ≠ i2 ∨ j1 ≠ j2)
        (honly : ∀ i j, i < m → j < n → cell grid i j = 1 →
          (i = i1 ∧ j = j1) ∨ (i = i2 ∧ j = j2)), ∃ r : Std.I64, count_servers grid = ok r ∧
          r.val = (if i1 = i2 ∨ j1 = j2 then (2 : ℤ) else 0)) := by
    sorry

  end AegisSpec.CountServers
