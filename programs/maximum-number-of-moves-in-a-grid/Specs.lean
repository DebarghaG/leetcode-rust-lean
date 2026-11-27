import Aegis.MaxMoves.Code.Funs

/-!
# Specifications of `Aegis.MaxMoves.max_moves`

LeetCode problem `maximum-number-of-moves-in-a-grid`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxMoves

  def emptyRow : alloc.vec.Vec Std.I64 := alloc.vec.Vec.new Std.I64

  def rowAt (grid : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : alloc.vec.Vec Std.I64 :=
    grid.val.getD i emptyRow

  def cell (grid : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Int :=
    ((rowAt grid i).val.getD j 0#i64).val

  def IsLegalPath (grid : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat)
      (s : Nat → Nat) : Prop :=
    k ≤ n - 1 ∧
    (∀ j, j ≤ k → s j < m) ∧
    (∀ j, j < k → s j ≤ s (j + 1) + 1 ∧ s (j + 1) ≤ s j + 1) ∧
    (∀ j, j < k → cell grid (s j) j < cell grid (s (j + 1)) (j + 1))

  def IsMaxMoves (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (r : Int) : Prop :=
    0 ≤ r ∧
    r ≤ (n : Int) - 1 ∧
    (∃ s : Nat → Nat, IsLegalPath grid m n r.toNat s) ∧
    (∀ k : Nat, (∃ s : Nat → Nat, IsLegalPath grid m n k s) → (k : Int) ≤ r)

  def InputsOk (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    grid.val.length = m ∧
    (∀ i, i < m → (rowAt grid i).val.length = n) ∧
    2 ≤ m ∧ m ≤ 1000 ∧
    2 ≤ n ∧ n ≤ 1000 ∧
    4 ≤ m * n ∧ m * n ≤ 100000 ∧
    (∀ i j, i < m → j < n → 1 ≤ cell grid i j ∧ cell grid i j ≤ 1000000)

  /-- The function returns a result r (max_moves(grid) = Result.ok r), and r = max { k | 0 <= k <= n-1 and there exist row indices s_0, ..., s_k such that: (i) 0 <= s_j < m for every j with 0 <= j <= k; (ii) |s_{j+1} - s_j| <= 1 for every j with 0 <= j < k; (iii) grid[s_j][j] < grid[s_{j+1}][j+1] for every j with 0 <= j < k }. The set is nonempty because k = 0 is allowed with any valid s_0.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n) :
      ∃ r : Std.I64, Aegis.MaxMoves.max_moves grid = ok r ∧ IsMaxMoves grid m n r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n), ∃ r : Std.I64, Aegis.MaxMoves.max_moves grid = ok r ∧ IsMaxMoves grid m n r.val) := by
    sorry

  /-- The function does not fail: there exists an integer r such that max_moves(grid) = Result.ok r. In particular, under the preconditions no index is out of bounds and no 64-bit arithmetic overflows.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n) :
      ∃ r : Std.I64, Aegis.MaxMoves.max_moves grid = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n), ∃ r : Std.I64, Aegis.MaxMoves.max_moves grid = ok r) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, we have 0 <= r <= n-1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      0 ≤ r.val ∧ r.val ≤ (n : Int) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), 0 ≤ r.val ∧ r.val ≤ (n : Int) - 1) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, there exists a legal path of exactly r moves, where a legal path of k moves is a sequence of row indices (s_0, ..., s_k) such that 0 <= k <= n-1, 0 <= s_j < m for all 0 <= j <= k, |s_{j+1} - s_j| <= 1 for all 0 <= j < k, and grid[s_j][j] < grid[s_{j+1}][j+1] for all 0 <= j < k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      ∃ s : Nat → Nat, IsLegalPath grid m n r.val.toNat s := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), ∃ s : Nat → Nat, IsLegalPath grid m n r.val.toNat s) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, for every k and every legal path of k moves, we have k <= r. Here a legal path of k moves is a sequence of row indices (s_0, ..., s_k) such that 0 <= k <= n-1, 0 <= s_j < m for all 0 <= j <= k, |s_{j+1} - s_j| <= 1 for all 0 <= j < k, and grid[s_j][j] < grid[s_{j+1}][j+1] for all 0 <= j < k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      ∀ (k : Nat) (s : Nat → Nat), IsLegalPath grid m n k s → (k : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), ∀ (k : Nat) (s : Nat → Nat), IsLegalPath grid m n k s → (k : Int) ≤ r.val) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, r = 0 if and only if there is no legal path of 1 move; equivalently, for every a,b with 0 <= a,b < m and |b-a| <= 1, grid[a][0] >= grid[b][1].
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      (r.val = 0 ↔
          ¬ ∃ a b : Nat, a < m ∧ b < m ∧ b ≤ a + 1 ∧ a ≤ b + 1 ∧ cell grid a 0 < cell grid b 1) ∧
        (r.val = 0 ↔
          ∀ a b : Nat, a < m → b < m → b ≤ a + 1 → a ≤ b + 1 → cell grid b 1 ≤ cell grid a 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), (r.val = 0 ↔
            ¬ ∃ a b : Nat, a < m ∧ b < m ∧ b ≤ a + 1 ∧ a ≤ b + 1 ∧ cell grid a 0 < cell grid b 1) ∧
          (r.val = 0 ↔
            ∀ a b : Nat, a < m → b < m → b ≤ a + 1 → a ≤ b + 1 → cell grid b 1 ≤ cell grid a 0)) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, for every integer k with 0 <= k <= r, there exists a legal path of exactly k moves, where a legal path of k moves is a sequence of row indices (s_0, ..., s_k) such that 0 <= k <= n-1, 0 <= s_j < m for all 0 <= j <= k, |s_{j+1} - s_j| <= 1 for all 0 <= j < k, and grid[s_j][j] < grid[s_{j+1}][j+1] for all 0 <= j < k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      ∀ k : Nat, (k : Int) ≤ r.val → ∃ s : Nat → Nat, IsLegalPath grid m n k s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), ∀ k : Nat, (k : Int) ≤ r.val → ∃ s : Nat → Nat, IsLegalPath grid m n k s) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, r = n-1 if and only if there exists a legal path of n-1 moves, where a legal path of k moves is a sequence of row indices (s_0, ..., s_k) such that 0 <= k <= n-1, 0 <= s_j < m for all 0 <= j <= k, |s_{j+1} - s_j| <= 1 for all 0 <= j < k, and grid[s_j][j] < grid[s_{j+1}][j+1] for all 0 <= j < k.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r) :
      (r.val = (n : Int) - 1 ↔ ∃ s : Nat → Nat, IsLegalPath grid m n (n - 1) s) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r), (r.val = (n : Int) - 1 ↔ ∃ s : Nat → Nat, IsLegalPath grid m n (n - 1) s)) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, if there exists a row s with 0 <= s < m such that grid[s][j] < grid[s][j+1] for every j with 0 <= j < n-1, then r = n-1.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
      (hrow : ∃ s : Nat, s < m ∧ ∀ j, j < n - 1 → cell grid s j < cell grid s (j + 1)) :
      r.val = (n : Int) - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
        (hrow : ∃ s : Nat, s < m ∧ ∀ j, j < n - 1 → cell grid s j < cell grid s (j + 1)), r.val = (n : Int) - 1) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, let grid_rev be the m x n matrix defined by grid_rev[i][j] = grid[m-1-i][j] for 0 <= i < m and 0 <= j < n. Then max_moves(grid_rev) = Result.ok r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
      (grid_rev : Slice (alloc.vec.Vec Std.I64))
      (hrev_len : grid_rev.val.length = m)
      (hrev_rows : ∀ i, i < m → (rowAt grid_rev i).val.length = n)
      (hrev_cells : ∀ i j, i < m → j < n → cell grid_rev i j = cell grid (m - 1 - i) j) :
      Aegis.MaxMoves.max_moves grid_rev = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
        (grid_rev : Slice (alloc.vec.Vec Std.I64))
        (hrev_len : grid_rev.val.length = m)
        (hrev_rows : ∀ i, i < m → (rowAt grid_rev i).val.length = n)
        (hrev_cells : ∀ i j, i < m → j < n → cell grid_rev i j = cell grid (m - 1 - i) j), Aegis.MaxMoves.max_moves grid_rev = ok r) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, for any integer c such that 1 <= grid[i][j]+c <= 1000000 for every 0 <= i < m and 0 <= j < n, let grid_shift[i][j] = grid[i][j]+c. Then max_moves(grid_shift) = Result.ok r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
      (c : Int)
      (hc : ∀ i j, i < m → j < n → 1 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
      (grid_shift : Slice (alloc.vec.Vec Std.I64))
      (hsft_len : grid_shift.val.length = m)
      (hsft_rows : ∀ i, i < m → (rowAt grid_shift i).val.length = n)
      (hsft_cells : ∀ i j, i < m → j < n → cell grid_shift i j = cell grid i j + c) :
      Aegis.MaxMoves.max_moves grid_shift = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
        (c : Int)
        (hc : ∀ i j, i < m → j < n → 1 ≤ cell grid i j + c ∧ cell grid i j + c ≤ 1000000)
        (grid_shift : Slice (alloc.vec.Vec Std.I64))
        (hsft_len : grid_shift.val.length = m)
        (hsft_rows : ∀ i, i < m → (rowAt grid_shift i).val.length = n)
        (hsft_cells : ∀ i j, i < m → j < n → cell grid_shift i j = cell grid i j + c), Aegis.MaxMoves.max_moves grid_shift = ok r) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, for every integer n' with 2 <= n' <= n, let grid_prefix be the m x n' matrix with grid_prefix[i][j] = grid[i][j] for 0 <= i < m and 0 <= j < n'. Then max_moves(grid_prefix) = Result.ok r' for some integer r' with r' <= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
      (n' : Nat) (hn'_lo : 2 ≤ n') (hn'_hi : n' ≤ n)
      (grid_prefix : Slice (alloc.vec.Vec Std.I64))
      (hpfx_len : grid_prefix.val.length = m)
      (hpfx_rows : ∀ i, i < m → (rowAt grid_prefix i).val.length = n')
      (hpfx_cells : ∀ i j, i < m → j < n' → cell grid_prefix i j = cell grid i j) :
      ∃ r' : Std.I64, Aegis.MaxMoves.max_moves grid_prefix = ok r' ∧ r'.val ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
        (n' : Nat) (hn'_lo : 2 ≤ n') (hn'_hi : n' ≤ n)
        (grid_prefix : Slice (alloc.vec.Vec Std.I64))
        (hpfx_len : grid_prefix.val.length = m)
        (hpfx_rows : ∀ i, i < m → (rowAt grid_prefix i).val.length = n')
        (hpfx_cells : ∀ i j, i < m → j < n' → cell grid_prefix i j = cell grid i j), ∃ r' : Std.I64, Aegis.MaxMoves.max_moves grid_prefix = ok r' ∧ r'.val ≤ r.val) := by
    sorry

  /-- Whenever max_moves(grid) = Result.ok r, let grid_ext be any matrix satisfying the same problem constraints, with the same number n of columns, with m' >= m rows, and with grid_ext[i][j] = grid[i][j] for all 0 <= i < m and 0 <= j < n. Then max_moves(grid_ext) = Result.ok r' for some integer r' with r' >= r.
    Preconditions: Let m = len(grid) and n = len(grid[0]). Assume 2 <= m <= 1000, 2 <= n <= 1000, every row grid[i] has length n, 4 <= m*n <= 100000, and 1 <= grid[i][j] <= 1000000 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
      (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
      (grid_ext : Slice (alloc.vec.Vec Std.I64)) (m' : Nat)
      (hext : InputsOk grid_ext m' n)
      (hm'_ge : m ≤ m')
      (hext_cells : ∀ i j, i < m → j < n → cell grid_ext i j = cell grid i j) :
      ∃ r' : Std.I64, Aegis.MaxMoves.max_moves grid_ext = ok r' ∧ r.val ≤ r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (h : InputsOk grid m n)
        (r : Std.I64) (hres : Aegis.MaxMoves.max_moves grid = ok r)
        (grid_ext : Slice (alloc.vec.Vec Std.I64)) (m' : Nat)
        (hext : InputsOk grid_ext m' n)
        (hm'_ge : m ≤ m')
        (hext_cells : ∀ i j, i < m → j < n → cell grid_ext i j = cell grid i j), ∃ r' : Std.I64, Aegis.MaxMoves.max_moves grid_ext = ok r' ∧ r.val ≤ r'.val) := by
    sorry

  end AegisSpec.MaxMoves
