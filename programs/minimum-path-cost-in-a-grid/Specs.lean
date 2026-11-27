import Aegis.MinPathCost.Code.Funs

/-!
# Specifications of `Aegis.MinPathCost.min_path_cost`

LeetCode problem `minimum-path-cost-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinPathCost

  abbrev Mat : Type := List (List Int)

  def matGet (l : Mat) (i j : Nat) : Int := (l.getD i []).getD j 0

  def gridMat (grid : Slice (alloc.vec.Vec Std.I64)) : Mat :=
    grid.val.map (fun row => row.val.map fun x => x.val)

  def costMat (moveCost : Slice (alloc.vec.Vec Std.I64)) : Mat :=
    moveCost.val.map (fun row => row.val.map fun x => x.val)

  def entries (l : Mat) : List Int := l.flatten

  def minOfList : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr min x

  def maxOfList : List Int → Int
    | [] => 0
    | x :: xs => xs.foldr max x

  def pathCost (mc : Mat) : Mat → List Nat → Int
    | g :: gs, c :: cs =>
        let v := g.getD c 0
        v +
          (match cs with
            | [] => 0
            | c' :: _ => matGet mc v.toNat c' + pathCost mc gs cs)
    | _, _ => 0

  def allPaths : Nat → Nat → List (List Nat)
    | 0, _ => [[]]
    | k + 1, n => (allPaths k n).flatMap fun cs => (List.range n).map fun c => c :: cs

  def specMinCost (g mc : Mat) (m n : Nat) : Int :=
    minOfList ((allPaths m n).map (pathCost mc g))

  def permuteRow (pi : Nat → Nat) (row : List Int) : List Int :=
    (List.range row.length).map fun j => row.getD (pi j) 0

  abbrev f := Aegis.MinPathCost.min_path_cost

  /-- The function returns a result r and r = min { sum_{k=0}^{m-1} grid[k][c_k] + sum_{k=0}^{m-2} moveCost[grid[k][c_k]][c_{k+1}] : for every k, 0 <= c_k < n }.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_1 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100) :
      ∃ r : Std.I64,
        f grid moveCost = ok r ∧
        r.val = specMinCost (gridMat grid) (costMat moveCost) m n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100), ∃ r : Std.I64,
          f grid moveCost = ok r ∧
          r.val = specMinCost (gridMat grid) (costMat moveCost) m n) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds indexing, or panic).
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_2 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100) :
      ∃ r : Std.I64, f grid moveCost = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100), ∃ r : Std.I64, f grid moveCost = ok r) := by
    sorry

  /-- The function returns a result r, and for every sequence of columns c_0,...,c_{m-1} with 0 <= c_k < n for all k, r <= sum_{k=0}^{m-1} grid[k][c_k] + sum_{k=0}^{m-2} moveCost[grid[k][c_k]][c_{k+1}].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_3 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100) :
      ∃ r : Std.I64,
        f grid moveCost = ok r ∧
        ∀ cs : List Nat, cs.length = m → (∀ c ∈ cs, c < n) →
          r.val ≤ pathCost (costMat moveCost) (gridMat grid) cs := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100), ∃ r : Std.I64,
          f grid moveCost = ok r ∧
          ∀ cs : List Nat, cs.length = m → (∀ c ∈ cs, c < n) →
            r.val ≤ pathCost (costMat moveCost) (gridMat grid) cs) := by
    sorry

  /-- The function returns a result r, and there exists a sequence of columns c_0,...,c_{m-1} with 0 <= c_k < n for all k such that r = sum_{k=0}^{m-1} grid[k][c_k] + sum_{k=0}^{m-2} moveCost[grid[k][c_k]][c_{k+1}].
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_4 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100) :
      ∃ r : Std.I64,
        f grid moveCost = ok r ∧
        ∃ cs : List Nat, cs.length = m ∧ (∀ c ∈ cs, c < n) ∧
          r.val = pathCost (costMat moveCost) (gridMat grid) cs := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100), ∃ r : Std.I64,
          f grid moveCost = ok r ∧
          ∃ cs : List Nat, cs.length = m ∧ (∀ c ∈ cs, c < n) ∧
            r.val = pathCost (costMat moveCost) (gridMat grid) cs) := by
    sorry

  /-- Let mu = min_{0 <= v < m*n, 0 <= j < n} moveCost[v][j]. The function returns a result r, and r >= sum_{k=0}^{m-1} min_{0 <= j < n} grid[k][j] + (m-1)*mu.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_5 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
      (mu : Int) (hmu : mu = minOfList (entries (costMat moveCost))) :
      ∃ r : Std.I64,
        f grid moveCost = ok r ∧
        ((gridMat grid).map minOfList).sum + ((m - 1 : Nat) : Int) * mu ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
        (mu : Int) (hmu : mu = minOfList (entries (costMat moveCost))), ∃ r : Std.I64,
          f grid moveCost = ok r ∧
          ((gridMat grid).map minOfList).sum + ((m - 1 : Nat) : Int) * mu ≤ r.val) := by
    sorry

  /-- Let r be the result of min_path_cost(grid, moveCost) and r' be the result of min_path_cost(grid', moveCost'). The function returns both results, and r = r'.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The original input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. Let pi be any permutation of {0,1,...,n-1}. Define grid' by grid'[i][j] = grid[i][pi(j)] for all i,j and moveCost' by moveCost'[v][j] = moveCost[v][pi(j)] for all v,j. -/
  theorem spec_6 (grid moveCost grid' moveCost' : Slice (alloc.vec.Vec Std.I64))
      (m n : Nat) (pi : Nat → Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
      (hpi_lt : ∀ j, j < n → pi j < n)
      (hpi_inj : ∀ j₁ j₂, j₁ < n → j₂ < n → pi j₁ = pi j₂ → j₁ = j₂)
      (hgrid' : gridMat grid' = (gridMat grid).map (permuteRow pi))
      (hmoveCost' : costMat moveCost' = (costMat moveCost).map (permuteRow pi)) :
      ∃ r r' : Std.I64,
        f grid moveCost = ok r ∧ f grid' moveCost' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid moveCost grid' moveCost' : Slice (alloc.vec.Vec Std.I64))
        (m n : Nat) (pi : Nat → Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
        (hpi_lt : ∀ j, j < n → pi j < n)
        (hpi_inj : ∀ j₁ j₂, j₁ < n → j₂ < n → pi j₁ = pi j₂ → j₁ = j₂)
        (hgrid' : gridMat grid' = (gridMat grid).map (permuteRow pi))
        (hmoveCost' : costMat moveCost' = (costMat moveCost).map (permuteRow pi)), ∃ r r' : Std.I64,
          f grid moveCost = ok r ∧ f grid' moveCost' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let r_A be the result of min_path_cost(grid, A) and r_B be the result of min_path_cost(grid, B). The function returns both results, and r_A <= r_B.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The grid satisfies: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}. Let A and B be two moveCost arrays with len(A) = len(B) = m*n, every row of A and of B of length n, all entries in {1,2,...,100}, and A[v][j] <= B[v][j] for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_7 (grid A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hA_len : A.val.length = m * n)
      (hB_len : B.val.length = m * n)
      (hA_rows : ∀ row ∈ A.val, row.val.length = n)
      (hB_rows : ∀ row ∈ B.val, row.val.length = n)
      (hA_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat A) v j ∧ matGet (costMat A) v j ≤ 100)
      (hB_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat B) v j ∧ matGet (costMat B) v j ≤ 100)
      (hle : ∀ v j, v < m * n → j < n →
        matGet (costMat A) v j ≤ matGet (costMat B) v j) :
      ∃ rA rB : Std.I64,
        f grid A = ok rA ∧ f grid B = ok rB ∧ rA.val ≤ rB.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid A B : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hA_len : A.val.length = m * n)
        (hB_len : B.val.length = m * n)
        (hA_rows : ∀ row ∈ A.val, row.val.length = n)
        (hB_rows : ∀ row ∈ B.val, row.val.length = n)
        (hA_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat A) v j ∧ matGet (costMat A) v j ≤ 100)
        (hB_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat B) v j ∧ matGet (costMat B) v j ≤ 100)
        (hle : ∀ v j, v < m * n → j < n →
          matGet (costMat A) v j ≤ matGet (costMat B) v j), ∃ rA rB : Std.I64,
          f grid A = ok rA ∧ f grid B = ok rB ∧ rA.val ≤ rB.val) := by
    sorry

  /-- Let M = max_{0 <= v < m*n, 0 <= j < n} moveCost[v][j]. The function returns a result r, and r <= sum_{k=0}^{m-1} min_{0 <= j < n} grid[k][j] + (m-1)*M.
    Preconditions: Let m = len(grid) and n = len(grid[0]). The input satisfies the problem constraints: 2 <= m <= 50, 2 <= n <= 50; every row of grid has length n; the m*n entries of grid are pairwise distinct and each lies in {0,1,...,m*n-1}; len(moveCost) = m*n; every row of moveCost has length n; and 1 <= moveCost[v][j] <= 100 for every 0 <= v < m*n and 0 <= j < n. -/
  theorem spec_8 (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm : grid.val.length = m)
      (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
      (hrows : ∀ row ∈ grid.val, row.val.length = n)
      (hnd : (entries (gridMat grid)).Nodup)
      (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
      (hmc_len : moveCost.val.length = m * n)
      (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
      (hmc_bounds : ∀ v j, v < m * n → j < n →
        1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
      (M : Int) (hM : M = maxOfList (entries (costMat moveCost))) :
      ∃ r : Std.I64,
        f grid moveCost = ok r ∧
        r.val ≤ ((gridMat grid).map minOfList).sum + ((m - 1 : Nat) : Int) * M := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid moveCost : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm : grid.val.length = m)
        (hm_lb : 2 ≤ m) (hm_ub : m ≤ 50)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 50)
        (hrows : ∀ row ∈ grid.val, row.val.length = n)
        (hnd : (entries (gridMat grid)).Nodup)
        (hrange : ∀ x ∈ entries (gridMat grid), 0 ≤ x ∧ x < ((m * n : Nat) : Int))
        (hmc_len : moveCost.val.length = m * n)
        (hmc_rows : ∀ row ∈ moveCost.val, row.val.length = n)
        (hmc_bounds : ∀ v j, v < m * n → j < n →
          1 ≤ matGet (costMat moveCost) v j ∧ matGet (costMat moveCost) v j ≤ 100)
        (M : Int) (hM : M = maxOfList (entries (costMat moveCost))), ∃ r : Std.I64,
          f grid moveCost = ok r ∧
          r.val ≤ ((gridMat grid).map minOfList).sum + ((m - 1 : Nat) : Int) * M) := by
    sorry

  end AegisSpec.MinPathCost
