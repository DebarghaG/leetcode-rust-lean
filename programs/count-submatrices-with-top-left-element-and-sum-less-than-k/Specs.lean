import Aegis.CountSubmatrices.Code.Funs

/-!
# Specifications of `Aegis.CountSubmatrices.count_submatrices`

LeetCode problem `count-submatrices-with-top-left-element-and-sum-less-than-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubmatrices

def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  match grid.val[i]? with
  | none => 0
  | some row =>
    match row.val[j]? with
    | none => 0
    | some x => x.val

def prefixSum (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), cell grid a b

def totalSum (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Int :=
  ∑ a ∈ Finset.range m, ∑ b ∈ Finset.range n, cell grid a b

def countRegion (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (kk : Int) : Nat :=
  (((Finset.range m) ×ˢ (Finset.range n)).filter
    (fun p : Nat × Nat => prefixSum grid p.1 p.2 ≤ kk)).card

def rowCount (grid : Slice (alloc.vec.Vec Std.I64)) (n : Nat) (kk : Int) (i : Nat) : Nat :=
  ((Finset.range n).filter (fun j => prefixSum grid i j ≤ kk)).card

/-- Whenever the function returns a result r, r = |{(i,j) : 0 <= i < m and 0 <= j < n and P(i,j) <= k}|, where P(i,j) = sum_{a=0}^{i} sum_{b=0}^{j} grid[a][b].
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_1
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      r.val = (countRegion grid m n k.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      r.val = (countRegion grid m n k.val : Int)) := by
  sorry

/-- Under the preconditions, the function returns a result r and does not fail (no overflow, out-of-bounds access, or panic).
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_2
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9) :
    ∃ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9), ∃ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_3
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      0 ≤ r.val ∧ r.val ≤ ((m * n : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if grid[0][0] > k. Equivalently, r > 0 if and only if grid[0][0] <= k.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_4
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9) :
    ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      ((r.val = 0 ↔ k.val < cell grid 0 0) ∧ (0 < r.val ↔ cell grid 0 0 ≤ k.val)) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9), ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      ((r.val = 0 ↔ k.val < cell grid 0 0) ∧ (0 < r.val ↔ cell grid 0 0 ≤ k.val))) := by
  sorry

/-- Whenever the function returns a result r, if k >= S where S = sum_{a=0}^{m-1} sum_{b=0}^{n-1} grid[a][b], then r = m*n.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_5
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (hS : totalSum grid m n ≤ k.val) :
    ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      r.val = ((m * n : Nat) : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (hS : totalSum grid m n ≤ k.val), ∀ r : Std.I64, Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      r.val = ((m * n : Nat) : Int)) := by
  sorry

/-- For every integer k' with k <= k' <= 10^9, whenever the function returns r on input (grid,k) and returns r' on input (grid,k'), we have r <= r'.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_6
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9) :
    ∀ (k' : Std.I64) (r r' : Std.I64),
      k.val ≤ k'.val → k'.val ≤ 10 ^ 9 →
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices grid k' = ok r' →
      r.val ≤ r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9), ∀ (k' : Std.I64) (r r' : Std.I64),
      k.val ≤ k'.val → k'.val ≤ 10 ^ 9 →
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices grid k' = ok r' →
      r.val ≤ r'.val) := by
  sorry

/-- Let H be the n-by-m matrix defined by H[i][j] = grid[j][i] for 0 <= i < n and 0 <= j < m. Whenever the function returns r on input (grid,k) and returns rT on input (H,k), we have r = rT.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_7
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (H : Slice (alloc.vec.Vec Std.I64))
    (hH_len : H.val.length = n) (hH_rows : ∀ row ∈ H.val, row.val.length = m)
    (hH : ∀ i j, i < n → j < m → cell H i j = cell grid j i) :
    ∀ r rT : Std.I64,
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices H k = ok rT →
      r.val = rT.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (H : Slice (alloc.vec.Vec Std.I64))
    (hH_len : H.val.length = n) (hH_rows : ∀ row ∈ H.val, row.val.length = m)
    (hH : ∀ i j, i < n → j < m → cell H i j = cell grid j i), ∀ r rT : Std.I64,
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices H k = ok rT →
      r.val = rT.val) := by
  sorry

/-- For every m-by-n matrix H such that 0 <= H[i][j] <= grid[i][j] for all i,j, whenever the function returns r on input (grid,k) and returns rH on input (H,k), we have rH >= r.
  Preconditions: Let m = len(grid) and n = len(grid[0]). Preconditions: m >= 1; every row of grid has length n, with n >= 1; m <= 1000 and n <= 1000; for every i,j with 0 <= i < m and 0 <= j < n, 0 <= grid[i][j] <= 1000; and 1 <= k <= 10^9. -/
theorem spec_8
    (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (H : Slice (alloc.vec.Vec Std.I64))
    (hH_len : H.val.length = m) (hH_rows : ∀ row ∈ H.val, row.val.length = n)
    (hH_cells : ∀ i j, i < m → j < n → 0 ≤ cell H i j ∧ cell H i j ≤ cell grid i j) :
    ∀ r rH : Std.I64,
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices H k = ok rH →
      r.val ≤ rH.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (k : Std.I64) (m n : Nat)
    (hm : 1 ≤ m) (hm_len : grid.val.length = m)
    (hn : 1 ≤ n) (hrows : ∀ row ∈ grid.val, row.val.length = n)
    (hm_bound : m ≤ 1000) (hn_bound : n ≤ 1000)
    (hcells : ∀ i j, i < m → j < n → 0 ≤ cell grid i j ∧ cell grid i j ≤ 1000)
    (hk_low : 1 ≤ k.val) (hk_high : k.val ≤ 10 ^ 9)
    (H : Slice (alloc.vec.Vec Std.I64))
    (hH_len : H.val.length = m) (hH_rows : ∀ row ∈ H.val, row.val.length = n)
    (hH_cells : ∀ i j, i < m → j < n → 0 ≤ cell H i j ∧ cell H i j ≤ cell grid i j), ∀ r rH : Std.I64,
      Aegis.CountSubmatrices.count_submatrices grid k = ok r →
      Aegis.CountSubmatrices.count_submatrices H k = ok rH →
      r.val ≤ rH.val) := by
  sorry

end AegisSpec.CountSubmatrices
