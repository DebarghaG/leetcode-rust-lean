import Aegis.DeleteGreatestValue.Code.Funs

/-!
# Specifications of `Aegis.DeleteGreatestValue.delete_greatest_value`

LeetCode problem `delete-greatest-value-in-each-row`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DeleteGreatestValue

  open Aegis.DeleteGreatestValue (delete_greatest_value)

  def rowsOf (grid : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    grid.val.map fun r => r.val.map fun x => x.val

  def nRows (grid : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    (rowsOf grid).length

  def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
    (rowsOf grid).getD i []

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    (rowAt grid i).getD j 0

  def GridValid (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
    nRows grid = m ∧ 1 ≤ m ∧ m ≤ 50 ∧ 1 ≤ n ∧ n ≤ 50 ∧
      (∀ i, i < m → (rowAt grid i).length = n) ∧
      (∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 100)

  def insertSortedDesc (x : ℤ) : List ℤ → List ℤ
    | [] => [x]
    | y :: ys => if y < x then x :: y :: ys else y :: insertSortedDesc x ys

  def sortDesc : List ℤ → List ℤ
    | [] => []
    | x :: xs => insertSortedDesc x (sortDesc xs)

  def kth (l : List ℤ) (k : ℕ) : ℤ :=
    if h : k - 1 < l.length then l.get ⟨k - 1, h⟩ else 0

  def dval (grid : Slice (alloc.vec.Vec Std.I64)) (i k : ℕ) : ℤ :=
    kth (sortDesc (rowAt grid i)) k

  def maxOver (m : ℕ) (f : ℕ → ℤ) : ℤ :=
    ((List.range m).map f).foldl max (f 0)

  def cval (grid : Slice (alloc.vec.Vec Std.I64)) (m k : ℕ) : ℤ :=
    maxOver m fun i => dval grid i k

  def answer (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : ℤ :=
    ∑ k ∈ Finset.Icc 1 n, cval grid m k

  def rowSum (grid : Slice (alloc.vec.Vec Std.I64)) (i n : ℕ) : ℤ :=
    ∑ j ∈ Finset.range n, cell grid i j

  def rowMin (grid : Slice (alloc.vec.Vec Std.I64)) (i n : ℕ) : ℤ :=
    ((List.range n).map fun j => cell grid i j).foldl min (cell grid i 0)

  /-- For each row i, sort grid[i] in non-increasing order and let d_i(k) be the k-th element of this sorted row (1 <= k <= n), counting multiplicities. Define c_k = max_{0 <= i < m} d_i(k) for 1 <= k <= n. The function returns a result r and r = sum_{k=1}^{n} c_k.
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) :
      ∃ r : Std.I64, delete_greatest_value grid = ok r ∧ r.val = answer grid m n := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n), ∃ r : Std.I64, delete_greatest_value grid = ok r ∧ r.val = answer grid m n) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or report an arithmetic overflow for any input satisfying the preconditions.
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) :
      ∃ r : Std.I64, delete_greatest_value grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n), ∃ r : Std.I64, delete_greatest_value grid = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= 100 * n. In particular r <= 5000.
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) :
      ∀ r : Std.I64, delete_greatest_value grid = ok r →
        r.val ≤ 100 * (n : ℤ) ∧ r.val ≤ 5000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n), ∀ r : Std.I64, delete_greatest_value grid = ok r →
          r.val ≤ 100 * (n : ℤ) ∧ r.val ≤ 5000) := by
    sorry

  /-- Whenever the function returns a result r, for every row i with 0 <= i < m, sum_{j=0}^{n-1} grid[i][j] <= r. Equivalently, r >= max_{0 <= i < m} sum_{j=0}^{n-1} grid[i][j].
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) :
      ∀ r : Std.I64, delete_greatest_value grid = ok r →
        (∀ i, i < m → rowSum grid i n ≤ r.val) ∧
          maxOver m (fun i => rowSum grid i n) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n), ∀ r : Std.I64, delete_greatest_value grid = ok r →
          (∀ i, i < m → rowSum grid i n ≤ r.val) ∧
            maxOver m (fun i => rowSum grid i n) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{j=0}^{n-1} grid[0][j].
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. For every i with 0 <= i < m, row grid[i] is a permutation of row grid[0]. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n)
      (hperm : ∀ i, i < m → (rowAt grid i).Perm (rowAt grid 0)) :
      ∀ r : Std.I64, delete_greatest_value grid = ok r → r.val = rowSum grid 0 n := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n)
        (hperm : ∀ i, i < m → (rowAt grid i).Perm (rowAt grid 0)), ∀ r : Std.I64, delete_greatest_value grid = ok r → r.val = rowSum grid 0 n) := by
    sorry

  /-- Whenever the function returns r on grid and r' on grid', r = r'.
    Preconditions: Both grid and grid' satisfy the problem constraints with the same dimensions m and n. There is a bijection p on {0,...,m-1} such that grid'[i] = grid[p(i)] for every 0 <= i < m. -/
  theorem spec_6 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) (h' : GridValid grid' m n)
      (hp : ∃ p : Equiv.Perm (Fin m), ∀ i (hi : i < m),
        rowAt grid' i = rowAt grid ((p ⟨i, hi⟩ : Fin m) : ℕ)) :
      ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
        delete_greatest_value grid' = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n) (h' : GridValid grid' m n)
        (hp : ∃ p : Equiv.Perm (Fin m), ∀ i (hi : i < m),
          rowAt grid' i = rowAt grid ((p ⟨i, hi⟩ : Fin m) : ℕ)), ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
          delete_greatest_value grid' = ok r' → r = r') := by
    sorry

  /-- Whenever the function returns r on grid and r' on grid', r <= r'.
    Preconditions: Both grid and grid' satisfy the problem constraints with the same dimensions m and n, and grid[i][j] <= grid'[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) (h' : GridValid grid' m n)
      (hle : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid' i j) :
      ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
        delete_greatest_value grid' = ok r' → r.val ≤ r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n) (h' : GridValid grid' m n)
        (hle : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid' i j), ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
          delete_greatest_value grid' = ok r' → r.val ≤ r'.val) := by
    sorry

  /-- Whenever the function returns r on grid and r' on grid', r' = r + n * t.
    Preconditions: Both grid and grid' satisfy the problem constraints with the same dimensions m and n, and there is an integer t such that grid'[i][j] = grid[i][j] + t for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (t : ℤ)
      (h : GridValid grid m n) (h' : GridValid grid' m n)
      (hshift : ∀ i j, i < m → j < n → cell grid' i j = cell grid i j + t) :
      ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
        delete_greatest_value grid' = ok r' → r'.val = r.val + (n : ℤ) * t := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (t : ℤ)
        (h : GridValid grid m n) (h' : GridValid grid' m n)
        (hshift : ∀ i j, i < m → j < n → cell grid' i j = cell grid i j + t), ∀ r r' : Std.I64, delete_greatest_value grid = ok r →
          delete_greatest_value grid' = ok r' → r'.val = r.val + (n : ℤ) * t) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{j=0}^{n-1} grid[a][j].
    Preconditions: grid satisfies the problem constraints with dimensions m and n. There is an index a with 0 <= a < m such that for every row i with 0 <= i < m and every column j with 0 <= j < n, grid[i][j] <= grid[a][j]. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (a : ℕ)
      (h : GridValid grid m n) (ha : a < m)
      (hdom : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid a j) :
      ∀ r : Std.I64, delete_greatest_value grid = ok r → r.val = rowSum grid a n := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (a : ℕ)
        (h : GridValid grid m n) (ha : a < m)
        (hdom : ∀ i j, i < m → j < n → cell grid i j ≤ cell grid a j), ∀ r : Std.I64, delete_greatest_value grid = ok r → r.val = rowSum grid a n) := by
    sorry

  /-- Whenever the function returns a result r, let d_i(k) and c_k be as in the main specification (so r = sum_{k=1}^{n} c_k). Then c_1 >= c_2 >= ... >= c_n.
    Preconditions: Let m = len(grid). There is an integer n with 1 <= m,n <= 50 such that len(grid[i]) = n for every 0 <= i < m, and 1 <= grid[i][j] <= 100 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (h : GridValid grid m n) :
      ∀ r : Std.I64, delete_greatest_value grid = ok r →
        r.val = answer grid m n ∧
          ∀ k, 1 ≤ k → k < n → cval grid m (k + 1) ≤ cval grid m k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (h : GridValid grid m n), ∀ r : Std.I64, delete_greatest_value grid = ok r →
          r.val = answer grid m n ∧
            ∀ k, 1 ≤ k → k < n → cval grid m (k + 1) ≤ cval grid m k) := by
    sorry

  end AegisSpec.DeleteGreatestValue
