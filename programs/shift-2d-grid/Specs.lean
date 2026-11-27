import Aegis.ShiftGrid.Code.Funs

/-!
# Specifications of `Aegis.ShiftGrid.shift_grid`

LeetCode problem `shift-2d-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ShiftGrid

  namespace AegisSpec.ShiftGrid

  def matOf (rows : List (alloc.vec.Vec I64)) : List (List Int) :=
    rows.map (fun row => row.val.map (fun x => x.val))

  def gridMat (grid : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    matOf grid.val

  def outMat (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List (List Int) :=
    matOf r.val

  def rowLen (M : List (List Int)) (i : Nat) : Nat :=
    (M.getD i []).length

  def entry (M : List (List Int)) (i j : Nat) : Int :=
    (M.getD i []).getD j 0

  def flat (M : List (List Int)) : List Int :=
    M.flatten

  def zrem (a : Int) (N : Nat) : Nat :=
    (a % (N : Int)).toNat

  /-- Let N = m * n and s = k mod N (the remainder in 0 <= s < N). The function returns a result r such that len(r) = m, len(r[i]) = n for every 0 <= i < m, and for every p with 0 <= p < N, writing q = (p + s) mod N, we have r[q / n][q % n] = grid[p / n][p % n]. Here p / n and p % n denote row-major division and remainder.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_1
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ p, p < m * n →
          let s := zrem k.val (m * n)
          let q := (p + s) % (m * n)
          entry (outMat r) (q / n) (q % n) = entry (gridMat grid) (p / n) (p % n)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ p, p < m * n →
            let s := zrem k.val (m * n)
            let q := (p + s) % (m * n)
            entry (outMat r) (q / n) (q % n) = entry (gridMat grid) (p / n) (p % n))) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_2
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r) := by
    sorry

  /-- The function returns a result r such that len(r) = m and for every i with 0 <= i < m, len(r[i]) = n.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_3
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n)) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and for every i with 0 <= i < m and every j with 0 <= j < n, r[i][j] = grid[i][j].
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. Additionally k mod (m * n) = 0. -/
  theorem spec_4
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
      (hzero : zrem k.val (m * n) = 0) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ i j, i < m → j < n →
          entry (outMat r) i j = entry (gridMat grid) i j) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
        (hzero : zrem k.val (m * n) = 0), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ i j, i < m → j < n →
            entry (outMat r) i j = entry (gridMat grid) i j)) := by
    sorry

  /-- The function returns a result r with len(r) = 1 and len(r[0]) = n, and for every j with 0 <= j < n, r[0][j] = grid[0][(j - (k mod n)) mod n].
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. Additionally m = 1. -/
  theorem spec_5
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
      (hmone : m = 1) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = 1 ∧
        rowLen (outMat r) 0 = n ∧
        (∀ j, j < n →
          entry (outMat r) 0 j
            = entry (gridMat grid) 0 (zrem ((j : Int) - (zrem k.val n : Int)) n)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
        (hmone : m = 1), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = 1 ∧
          rowLen (outMat r) 0 = n ∧
          (∀ j, j < n →
            entry (outMat r) 0 j
              = entry (gridMat grid) 0 (zrem ((j : Int) - (zrem k.val n : Int)) n))) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = 1 for every 0 <= i < m, and for every i with 0 <= i < m, r[i][0] = grid[(i - (k mod m)) mod m][0].
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. Additionally n = 1. -/
  theorem spec_6
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
      (hnone : n = 1) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = 1) ∧
        (∀ i, i < m →
          entry (outMat r) i 0
            = entry (gridMat grid) (zrem ((i : Int) - (zrem k.val m : Int)) m) 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
        (hnone : n = 1), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = 1) ∧
          (∀ i, i < m →
            entry (outMat r) i 0
              = entry (gridMat grid) (zrem ((i : Int) - (zrem k.val m : Int)) m) 0)) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and for every i,j with 0 <= i < m and 0 <= j < n: if j > 0 then r[i][j] = grid[i][j - 1]; if j = 0 and i > 0 then r[i][0] = grid[i - 1][n - 1]; if i = 0 and j = 0 then r[0][0] = grid[m - 1][n - 1].
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. Additionally k mod (m * n) = 1. -/
  theorem spec_7
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
      (hone : zrem k.val (m * n) = 1) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ i j, i < m → j < n → 0 < j →
          entry (outMat r) i j = entry (gridMat grid) i (j - 1)) ∧
        (∀ i j, i < m → j < n → j = 0 → 0 < i →
          entry (outMat r) i 0 = entry (gridMat grid) (i - 1) (n - 1)) ∧
        (entry (outMat r) 0 0 = entry (gridMat grid) (m - 1) (n - 1)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
        (hone : zrem k.val (m * n) = 1), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ i j, i < m → j < n → 0 < j →
            entry (outMat r) i j = entry (gridMat grid) i (j - 1)) ∧
          (∀ i j, i < m → j < n → j = 0 → 0 < i →
            entry (outMat r) i 0 = entry (gridMat grid) (i - 1) (n - 1)) ∧
          (entry (outMat r) 0 0 = entry (gridMat grid) (m - 1) (n - 1))) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = grid[(i - t) mod m][j], where t = (k / n) mod m and k / n is exact integer division because k mod n = 0.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. Additionally n >= 2, k mod n = 0, and, letting t = (k / n) mod m, t != 0. -/
  theorem spec_8
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
      (hn2 : 2 ≤ n)
      (hkmod : zrem k.val n = 0)
      (t : Nat)
      (ht : t = zrem (k.val / (n : Int)) m)
      (ht0 : t ≠ 0) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ i j, i < m → j < n →
          entry (outMat r) i j = entry (gridMat grid) (zrem ((i : Int) - (t : Int)) m) j) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100)
        (hn2 : 2 ≤ n)
        (hkmod : zrem k.val n = 0)
        (t : Nat)
        (ht : t = zrem (k.val / (n : Int)) m)
        (ht0 : t ≠ 0), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ i j, i < m → j < n →
            entry (outMat r) i j = entry (gridMat grid) (zrem ((i : Int) - (t : Int)) m) j)) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and the multiset of all entries of r, namely { r[i][j] | 0 <= i < m and 0 <= j < n }, is equal to the multiset { grid[i][j] | 0 <= i < m and 0 <= j < n }.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_9
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        List.Perm (flat (outMat r)) (flat (gridMat grid)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          List.Perm (flat (outMat r)) (flat (gridMat grid))) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= r[i][j] <= 1000.
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_10
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ i j, i < m → j < n →
          -1000 ≤ entry (outMat r) i j ∧ entry (outMat r) i j ≤ 1000) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ i j, i < m → j < n →
            -1000 ≤ entry (outMat r) i j ∧ entry (outMat r) i j ≤ 1000)) := by
    sorry

  /-- The function returns a result r with len(r) = m and len(r[i]) = n for every 0 <= i < m, and for every i,j with 0 <= i < m and 0 <= j < n, there exist a,b with 0 <= a < m and 0 <= b < n such that r[i][j] = grid[a][b].
    Preconditions: Let m = len(grid). The input satisfies: 1 <= m <= 50; let n = len(grid[0]) (well-defined since m >= 1); 1 <= n <= 50; for every i with 0 <= i < m, len(grid[i]) = n; for every i with 0 <= i < m and every j with 0 <= j < n, -1000 <= grid[i][j] <= 1000; and 0 <= k <= 100. -/
  theorem spec_11
      (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
      (hm : m = grid.val.length)
      (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
      (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
      (hn0 : rowLen (gridMat grid) 0 = n)
      (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
      (hbounds : ∀ i j, i < m → j < n →
        -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
      (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100) :
      ∃ r, shift_grid grid k = ok r ∧
        (outMat r).length = m ∧
        (∀ i, i < m → rowLen (outMat r) i = n) ∧
        (∀ i j, i < m → j < n →
          ∃ a b, a < m ∧ b < n ∧
            entry (outMat r) i j = entry (gridMat grid) a b) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (m n : Nat)
        (hm : m = grid.val.length)
        (hm1 : 1 ≤ m) (hm50 : m ≤ 50)
        (hn1 : 1 ≤ n) (hn50 : n ≤ 50)
        (hn0 : rowLen (gridMat grid) 0 = n)
        (hrows : ∀ i, i < m → rowLen (gridMat grid) i = n)
        (hbounds : ∀ i j, i < m → j < n →
          -1000 ≤ entry (gridMat grid) i j ∧ entry (gridMat grid) i j ≤ 1000)
        (hk0 : 0 ≤ k.val) (hk100 : k.val ≤ 100), ∃ r, shift_grid grid k = ok r ∧
          (outMat r).length = m ∧
          (∀ i, i < m → rowLen (outMat r) i = n) ∧
          (∀ i j, i < m → j < n →
            ∃ a b, a < m ∧ b < n ∧
              entry (outMat r) i j = entry (gridMat grid) a b)) := by
    sorry

  end AegisSpec.ShiftGrid
