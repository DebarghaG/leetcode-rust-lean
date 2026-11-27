import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-operations-to-make-columns-strictly-increasing`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperations

  def entry (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((grid.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))).getD 0

  def gridSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, entry grid i j

  def incrementSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (A : Nat → Nat → Int) : Int :=
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (A i j - entry grid i j)

  def Feasible (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (A : Nat → Nat → Int) : Prop :=
    (∀ i j, i < m → j < n → entry grid i j ≤ A i j) ∧
    (∀ i j, 1 ≤ i → i < m → j < n → A (i - 1) j < A i j)

  def ColFeasible (grid : Slice (alloc.vec.Vec Std.I64)) (m j : Nat) (b : Nat → Int) : Prop :=
    (∀ i, i < m → entry grid i j ≤ b i) ∧
    (∀ i, 1 ≤ i → i < m → b (i - 1) < b i)

  def colIncrementSum (grid : Slice (alloc.vec.Vec Std.I64)) (m j : Nat) (b : Nat → Int) : Int :=
    ∑ i ∈ Finset.range m, (b i - entry grid i j)

  def ColMin (grid : Slice (alloc.vec.Vec Std.I64)) (m j : Nat) (c : Int) : Prop :=
    (∃ b, ColFeasible grid m j b ∧ colIncrementSum grid m j b = c) ∧
    (∀ b, ColFeasible grid m j b → c ≤ colIncrementSum grid m j b)

  def greedy (grid : Slice (alloc.vec.Vec Std.I64)) : Nat → Nat → Int
    | 0, j => entry grid 0 j
    | (i + 1), j => max (entry grid (i + 1) j) (greedy grid i j + 1)

  /-- The function returns a result r, and r is equal to the minimum, over all m x n integer matrices A such that (i) A[i][j] >= grid[i][j] for every 0 <= i < m and 0 <= j < n, and (ii) A[i][j] > A[i-1][j] for every 1 <= i < m and 0 <= j < n, of the total increment sum Σ_{i=0}^{m-1} Σ_{j=0}^{n-1} (A[i][j] - grid[i][j]).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        (∀ A, Feasible grid m n A → r.val ≤ incrementSum grid m n A) ∧
        (∃ A, Feasible grid m n A ∧ incrementSum grid m n A = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          (∀ A, Feasible grid m n A → r.val ≤ incrementSum grid m n A) ∧
          (∃ A, Feasible grid m n A ∧ incrementSum grid m n A = r.val)) := by
    sorry

  /-- For every grid satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r) := by
    sorry

  /-- For every grid satisfying the preconditions, the returned result r satisfies r <= n * (Σ_{i=0}^{m-1} (2500 + i)) - Σ_{i=0}^{m-1} Σ_{j=0}^{n-1} grid[i][j].
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        r.val ≤ (n : Int) * (∑ i ∈ Finset.range m, ((2500 : Int) + (i : Int))) -
          gridSum grid m n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          r.val ≤ (n : Int) * (∑ i ∈ Finset.range m, ((2500 : Int) + (i : Int))) -
            gridSum grid m n) := by
    sorry

  /-- For each column j, let C_j be the minimum, over all length-m integer sequences b with b[i] >= grid[i][j] for every 0 <= i < m and b[i] > b[i-1] for every 1 <= i < m, of Σ_{i=0}^{m-1} (b[i] - grid[i][j]). Then the function returns a result r and r = Σ_{j=0}^{n-1} C_j.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
      (C : Nat → Int) (hC : ∀ j, j < n → ColMin grid m j (C j)) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        r.val = ∑ j ∈ Finset.range n, C j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
        (C : Nat → Int) (hC : ∀ j, j < n → ColMin grid m j (C j)), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          r.val = ∑ j ∈ Finset.range n, C j) := by
    sorry

  /-- For every grid satisfying the preconditions, the function returns a result r and r = 0 if and only if grid[i][j] > grid[i-1][j] for every 1 <= i < m and every 0 <= j < n.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        (r.val = 0 ↔ ∀ i j, 1 ≤ i → i < m → j < n → entry grid (i - 1) j < entry grid i j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          (r.val = 0 ↔ ∀ i j, 1 ≤ i → i < m → j < n → entry grid (i - 1) j < entry grid i j)) := by
    sorry

  /-- For every grid satisfying the preconditions, the function returns a result r and r = n * m * (m - 1) / 2.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. Also assume that for each column j there is an integer x_j such that grid[i][j] = x_j for every 0 <= i < m. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
      (hconst : ∀ j, j < n → ∃ x, ∀ i, i < m → entry grid i j = x) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        r.val = (n : Int) * (m : Int) * ((m : Int) - 1) / 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
        (hconst : ∀ j, j < n → ∃ x, ∀ i, i < m → entry grid i j = x), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          r.val = (n : Int) * (m : Int) * ((m : Int) - 1) / 2) := by
    sorry

  /-- Let r be the result on grid and r' be the result on grid'. The function returns both results and r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. Let k_0,...,k_{n-1} be integers and define grid'[i][j] = grid[i][j] + k_j. Assume grid' also satisfies the same standing constraints: every row has length n and 0 <= grid'[i][j] < 2500 for all i,j. -/
  theorem spec_7 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Nat → Int)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
      (hm' : grid'.val.length = m)
      (hrows' : ∀ i, i < m → ∃ row, grid'.val[i]? = some row ∧ row.val.length = n)
      (hentries' : ∀ i j, i < m → j < n → 0 ≤ entry grid' i j ∧ entry grid' i j < 2500)
      (hshift : ∀ i j, i < m → j < n → entry grid' i j = entry grid i j + k j) :
      ∃ r r', Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        Aegis.MinimumOperations.minimum_operations grid' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (k : Nat → Int)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500)
        (hm' : grid'.val.length = m)
        (hrows' : ∀ i, i < m → ∃ row, grid'.val[i]? = some row ∧ row.val.length = n)
        (hentries' : ∀ i j, i < m → j < n → 0 ≤ entry grid' i j ∧ entry grid' i j < 2500)
        (hshift : ∀ i j, i < m → j < n → entry grid' i j = entry grid i j + k j), ∃ r r', Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          Aegis.MinimumOperations.minimum_operations grid' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- For every grid satisfying the preconditions, the returned result r satisfies r >= max({0} ∪ {grid[i-1][j] + 1 - grid[i][j] | 1 <= i < m and 0 <= j < n}).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        0 ≤ r.val ∧
        (∀ i j, 1 ≤ i → i < m → j < n → entry grid (i - 1) j + 1 - entry grid i j ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          0 ≤ r.val ∧
          (∀ i j, 1 ≤ i → i < m → j < n → entry grid (i - 1) j + 1 - entry grid i j ≤ r.val)) := by
    sorry

  /-- The function returns a result r, and there exists an m x n integer matrix A such that: (i) A[i][j] >= grid[i][j] for all i,j; (ii) A[i][j] > A[i-1][j] for all 1 <= i < m and all j; (iii) Σ_{i=0}^{m-1} Σ_{j=0}^{n-1} (A[i][j] - grid[i][j]) = r; (iv) A[0][j] = grid[0][j] for every column j; and (v) for every 1 <= i < m and every column j, either A[i][j] = grid[i][j] or A[i][j] = A[i-1][j] + 1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        ∃ A, Feasible grid m n A ∧ incrementSum grid m n A = r.val ∧
          (∀ j, j < n → A 0 j = entry grid 0 j) ∧
          (∀ i j, 1 ≤ i → i < m → j < n →
            A i j = entry grid i j ∨ A i j = A (i - 1) j + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          ∃ A, Feasible grid m n A ∧ incrementSum grid m n A = r.val ∧
            (∀ j, j < n → A 0 j = entry grid 0 j) ∧
            (∀ i j, 1 ≤ i → i < m → j < n →
              A i j = entry grid i j ∨ A i j = A (i - 1) j + 1)) := by
    sorry

  /-- The function returns a result r, and for every m x n integer matrix A satisfying A[i][j] >= grid[i][j] for all i,j and A[i][j] > A[i-1][j] for all 1 <= i < m and all j, we have Σ_{i=0}^{m-1} Σ_{j=0}^{n-1} (A[i][j] - grid[i][j]) >= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        (∀ A, Feasible grid m n A → incrementSum grid m n A ≥ r.val) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          (∀ A, Feasible grid m n A → incrementSum grid m n A ≥ r.val)) := by
    sorry

  /-- Let r, r1, r2 be the results of the function on grid, G1, G2 respectively. The function returns all three results and r = r1 + r2.
    Preconditions: Let m,n1,n2 be positive integers with m,n1,n2 <= 50 and n1 + n2 <= 50. Let G1 be an m x n1 grid and G2 be an m x n2 grid, each satisfying the entry bounds 0 <= G1[i][j] < 2500 and 0 <= G2[i][j] < 2500 for all valid i,j. Let grid be the m x (n1+n2) horizontal concatenation: grid[i][j] = G1[i][j] for 0 <= j < n1, and grid[i][n1+j] = G2[i][j] for 0 <= j < n2. -/
  theorem spec_11 (G1 G2 grid : Slice (alloc.vec.Vec Std.I64)) (m n1 n2 : Nat)
      (hm1 : G1.val.length = m) (hm2 : G2.val.length = m) (hm : grid.val.length = m)
      (hrows1 : ∀ i, i < m → ∃ row, G1.val[i]? = some row ∧ row.val.length = n1)
      (hrows2 : ∀ i, i < m → ∃ row, G2.val[i]? = some row ∧ row.val.length = n2)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n1 + n2)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50)
      (hn1pos : 1 ≤ n1) (hn1le : n1 ≤ 50)
      (hn2pos : 1 ≤ n2) (hn2le : n2 ≤ 50) (hns : n1 + n2 ≤ 50)
      (hentries1 : ∀ i j, i < m → j < n1 → 0 ≤ entry G1 i j ∧ entry G1 i j < 2500)
      (hentries2 : ∀ i j, i < m → j < n2 → 0 ≤ entry G2 i j ∧ entry G2 i j < 2500)
      (hcat1 : ∀ i j, i < m → j < n1 → entry grid i j = entry G1 i j)
      (hcat2 : ∀ i j, i < m → j < n2 → entry grid i (n1 + j) = entry G2 i j) :
      ∃ r r1 r2, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        Aegis.MinimumOperations.minimum_operations G1 = ok r1 ∧
        Aegis.MinimumOperations.minimum_operations G2 = ok r2 ∧
        r.val = r1.val + r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (G1 G2 grid : Slice (alloc.vec.Vec Std.I64)) (m n1 n2 : Nat)
        (hm1 : G1.val.length = m) (hm2 : G2.val.length = m) (hm : grid.val.length = m)
        (hrows1 : ∀ i, i < m → ∃ row, G1.val[i]? = some row ∧ row.val.length = n1)
        (hrows2 : ∀ i, i < m → ∃ row, G2.val[i]? = some row ∧ row.val.length = n2)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n1 + n2)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50)
        (hn1pos : 1 ≤ n1) (hn1le : n1 ≤ 50)
        (hn2pos : 1 ≤ n2) (hn2le : n2 ≤ 50) (hns : n1 + n2 ≤ 50)
        (hentries1 : ∀ i j, i < m → j < n1 → 0 ≤ entry G1 i j ∧ entry G1 i j < 2500)
        (hentries2 : ∀ i j, i < m → j < n2 → 0 ≤ entry G2 i j ∧ entry G2 i j < 2500)
        (hcat1 : ∀ i j, i < m → j < n1 → entry grid i j = entry G1 i j)
        (hcat2 : ∀ i j, i < m → j < n2 → entry grid i (n1 + j) = entry G2 i j), ∃ r r1 r2, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          Aegis.MinimumOperations.minimum_operations G1 = ok r1 ∧
          Aegis.MinimumOperations.minimum_operations G2 = ok r2 ∧
          r.val = r1.val + r2.val) := by
    sorry

  /-- For each column j define b[0][j] = grid[0][j] and b[i][j] = max(grid[i][j], b[i-1][j] + 1) for 1 <= i < m. Then the function returns a result r and r = Σ_{i=0}^{m-1} Σ_{j=0}^{n-1} (b[i][j] - grid[i][j]).
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume m and n are positive integers with 1 <= m,n <= 50, every row grid[i] has length n, and 0 <= grid[i][j] < 2500 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
      (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
      (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500) :
      ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
        r.val = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
          (greedy grid i j - entry grid i j) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hrows : ∀ i, i < m → ∃ row, grid.val[i]? = some row ∧ row.val.length = n)
        (hmpos : 1 ≤ m) (hmle : m ≤ 50) (hnpos : 1 ≤ n) (hnle : n ≤ 50)
        (hentries : ∀ i j, i < m → j < n → 0 ≤ entry grid i j ∧ entry grid i j < 2500), ∃ r, Aegis.MinimumOperations.minimum_operations grid = ok r ∧
          r.val = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
            (greedy grid i j - entry grid i j)) := by
    sorry

  end AegisSpec.MinimumOperations
