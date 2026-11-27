import Aegis.NumberOfPaths.Code.Funs

/-!
# Specifications of `Aegis.NumberOfPaths.number_of_paths`

LeetCode problem `paths-in-matrix-whose-sum-is-divisible-by-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfPaths

  def MOD : ℕ := 1000000007

  def Rows (grid : Slice (alloc.vec.Vec I64)) : ℕ := grid.val.length

  def Cols (grid : Slice (alloc.vec.Vec I64)) : ℕ :=
    match grid.val with
    | [] => 0
    | row :: _ => row.val.length

  def get (grid : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
    match grid.val[i]? with
    | none => 0
    | some row =>
      match row.val[j]? with
      | none => 0
      | some v => v.val

  def kNat (k : I64) : ℕ := k.val.natAbs

  def walkSum (g : ℕ → ℕ → ℤ) : List Bool → ℕ → ℕ → ℤ
    | [], i, j => g i j
    | true :: rest, i, j => g i j + walkSum g rest (i + 1) j
    | false :: rest, i, j => g i j + walkSum g rest i (j + 1)

  def IsPathWord (m n : ℕ) (steps : Fin (m + n - 2) → Bool) : Prop :=
    (Finset.univ.filter (fun s : Fin (m + n - 2) => steps s = true)).card = m - 1

  instance instDecidableIsPathWord (m n : ℕ) (steps : Fin (m + n - 2) → Bool) :
      Decidable (IsPathWord m n steps) := by
    unfold IsPathWord
    infer_instance

  def numPaths (m n : ℕ) : ℕ :=
    (Finset.univ.filter (fun steps : Fin (m + n - 2) → Bool => IsPathWord m n steps)).card

  def numGoodPaths (g : ℕ → ℕ → ℤ) (m n k : ℕ) : ℕ :=
    (Finset.univ.filter (fun steps : Fin (m + n - 2) → Bool =>
      IsPathWord m n steps ∧ (k : ℤ) ∣ walkSum g (List.ofFn steps) 0 0)).card

  def existsGoodPath (g : ℕ → ℕ → ℤ) (m n k : ℕ) : Prop :=
    ∃ steps : Fin (m + n - 2) → Bool,
      IsPathWord m n steps ∧ (k : ℤ) ∣ walkSum g (List.ofFn steps) 0 0

  def ValidInput (grid : Slice (alloc.vec.Vec I64)) (k : I64) : Prop :=
    1 ≤ Rows grid ∧ Rows grid ≤ 50000 ∧
    1 ≤ Cols grid ∧ Cols grid ≤ 50000 ∧
    Rows grid * Cols grid ≤ 50000 ∧
    (∀ row, row ∈ grid.val → row.val.length = Cols grid) ∧
    (∀ row, row ∈ grid.val → ∀ v, v ∈ row.val → 0 ≤ v.val ∧ v.val ≤ 100) ∧
    1 ≤ k.val ∧ k.val ≤ 50

  def Entrywise (g g' : Slice (alloc.vec.Vec I64)) (f : ℤ → ℤ) : Prop :=
    Rows g' = Rows g ∧ Cols g' = Cols g ∧ ∀ i j, get g' i j = f (get g i j)

  def AgreesExceptAt (g g' : Slice (alloc.vec.Vec I64)) (i0 j0 : ℕ) : Prop :=
    Rows g' = Rows g ∧ Cols g' = Cols g ∧
      ∀ i j, (i ≠ i0 ∨ j ≠ j0) → get g' i j = get g i j

  def IsTranspose (g gT : Slice (alloc.vec.Vec I64)) : Prop :=
    Rows gT = Cols g ∧ Cols gT = Rows g ∧ ∀ i j, get gT j i = get g i j

  def IsRot180 (g gR : Slice (alloc.vec.Vec I64)) : Prop :=
    Rows gR = Rows g ∧ Cols gR = Cols g ∧
      ∀ i j, get gR i j = get g (Rows g - 1 - i) (Cols g - 1 - j)

  /-- The function returns a result r and r = N mod M, where M = 1000000007 and N is the number of monotone paths from (0,0) to (m-1,n-1) that move only one cell down or one cell right at each step and whose visited-cell sum, including both endpoints, is divisible by k.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_1 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = ((numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) % MOD : ℕ) : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = ((numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) % MOD : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_2 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) :
      ∀ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          0 ≤ r.val ∧ r.val < (MOD : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k), ∀ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            0 ≤ r.val ∧ r.val < (MOD : ℤ)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result and does not fail from arithmetic overflow, out-of-bounds access, or panic.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_3 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) :
      ∃ r : I64, Aegis.NumberOfPaths.number_of_paths grid k = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k), ∃ r : I64, Aegis.NumberOfPaths.number_of_paths grid k = ok r) := by
    sorry

  /-- Let grid' be the m by n matrix defined by grid'[i][j] = grid[i][j] mod k, using the remainder in the range 0 to k-1. If the function returns r on grid and r' on grid', both with the same k, then r = r'.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_4 (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (h' : Entrywise grid grid' (fun x => x % k.val)) :
      ∀ r r' : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r' := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (h' : Entrywise grid grid' (fun x => x % k.val)), ∀ r r' : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r') := by
    sorry

  /-- For every index pair (i0,j0) with 0 <= i0 < m and 0 <= j0 < n, and every integer c such that 0 <= grid[i0][j0] + c*k <= 100, let grid' be identical to grid except that grid'[i0][j0] = grid[i0][j0] + c*k. If the function returns r on grid and r' on grid', then r = r'.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_5 (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (i0 j0 : ℕ) (hi0 : i0 < Rows grid) (hj0 : j0 < Cols grid) (c : ℤ)
      (hlo : 0 ≤ get grid i0 j0 + c * k.val) (hhi : get grid i0 j0 + c * k.val ≤ 100)
      (h' : AgreesExceptAt grid grid' i0 j0)
      (hval : get grid' i0 j0 = get grid i0 j0 + c * k.val) :
      ∀ r r' : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (i0 j0 : ℕ) (hi0 : i0 < Rows grid) (hj0 : j0 < Cols grid) (c : ℤ)
        (hlo : 0 ≤ get grid i0 j0 + c * k.val) (hhi : get grid i0 j0 + c * k.val ≤ 100)
        (h' : AgreesExceptAt grid grid' i0 j0)
        (hval : get grid' i0 j0 = get grid i0 j0 + c * k.val), ∀ r r' : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r') := by
    sorry

  /-- Let gridT be the transpose of grid, so gridT has n rows and m columns and gridT[j][i] = grid[i][j] for all valid i,j. If the function returns r on grid and rT on gridT, both with the same k, then r = rT.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_6 (grid gridT : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hT : IsTranspose grid gridT) :
      ∀ r rT : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          Aegis.NumberOfPaths.number_of_paths gridT k = ok rT → r = rT := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (grid gridT : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hT : IsTranspose grid gridT), ∀ r rT : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            Aegis.NumberOfPaths.number_of_paths gridT k = ok rT → r = rT) := by
    sorry

  /-- The function returns r and r = P mod 1000000007, where P is the total number of monotone paths from (0,0) to (m-1,n-1) moving only down or right, with no divisibility restriction.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, for every i,j, k divides grid[i][j]. -/
  theorem spec_7 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hk : ∀ i j, (k.val : ℤ) ∣ get grid i j) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = ((numPaths (Rows grid) (Cols grid) % MOD : ℕ) : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hk : ∀ i j, (k.val : ℤ) ∣ get grid i j), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = ((numPaths (Rows grid) (Cols grid) % MOD : ℕ) : ℤ)) := by
    sorry

  /-- Let P be the total number of monotone paths from (0,0) to (m-1,n-1) moving only down or right. If k divides (m+n-1)*c, then the function returns r = P mod 1000000007; otherwise the function returns r = 0.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, there is an integer c with 0 <= c <= 100 such that grid[i][j] = c for every i,j. -/
  theorem spec_8 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) (c : ℤ)
      (hc0 : 0 ≤ c) (hc1 : c ≤ 100) (hconst : ∀ i j, get grid i j = c) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = (if (k.val : ℤ) ∣ ((Rows grid + Cols grid - 1 : ℕ) : ℤ) * c
                   then ((numPaths (Rows grid) (Cols grid) % MOD : ℕ) : ℤ) else 0) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) (c : ℤ)
        (hc0 : 0 ≤ c) (hc1 : c ≤ 100) (hconst : ∀ i j, get grid i j = c), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = (if (k.val : ℤ) ∣ ((Rows grid + Cols grid - 1 : ℕ) : ℤ) * c
                     then ((numPaths (Rows grid) (Cols grid) % MOD : ℕ) : ℤ) else 0)) := by
    sorry

  /-- The function returns r, where r = 1 if k divides grid[0][0], and r = 0 otherwise.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, m = 1 and n = 1. -/
  theorem spec_9 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hm : Rows grid = 1) (hn : Cols grid = 1) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = (if (k.val : ℤ) ∣ get grid 0 0 then (1 : ℤ) else 0) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hm : Rows grid = 1) (hn : Cols grid = 1), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = (if (k.val : ℤ) ∣ get grid 0 0 then (1 : ℤ) else 0)) := by
    sorry

  /-- Let S = grid[0][0] + grid[0][1] + ... + grid[0][n-1] be the sum of the single row. The function returns r, where r = 1 if k divides S, and r = 0 otherwise.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, m = 1 and n >= 2. -/
  theorem spec_10 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hm : Rows grid = 1) (hn : 2 ≤ Cols grid) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = (if (k.val : ℤ) ∣ ∑ j ∈ Finset.range (Cols grid), get grid 0 j
                   then (1 : ℤ) else 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hm : Rows grid = 1) (hn : 2 ≤ Cols grid), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = (if (k.val : ℤ) ∣ ∑ j ∈ Finset.range (Cols grid), get grid 0 j
                     then (1 : ℤ) else 0)) := by
    sorry

  /-- Let S = grid[0][0] + grid[1][0] + ... + grid[m-1][0] be the sum of the single column. The function returns r, where r = 1 if k divides S, and r = 0 otherwise.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, n = 1 and m >= 2. -/
  theorem spec_11 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hn : Cols grid = 1) (hm : 2 ≤ Rows grid) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = (if (k.val : ℤ) ∣ ∑ i ∈ Finset.range (Rows grid), get grid i 0
                   then (1 : ℤ) else 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hn : Cols grid = 1) (hm : 2 ≤ Rows grid), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = (if (k.val : ℤ) ∣ ∑ i ∈ Finset.range (Rows grid), get grid i 0
                     then (1 : ℤ) else 0)) := by
    sorry

  /-- Define A = grid[0][0] + grid[0][1] + grid[1][1] and B = grid[0][0] + grid[1][0] + grid[1][1]. The function returns r = (1 if k divides A else 0) + (1 if k divides B else 0).
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. Moreover, m = 2 and n = 2. -/
  theorem spec_12 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hm : Rows grid = 2) (hn : Cols grid = 2) :
      ∃ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
          r.val = (if (k.val : ℤ) ∣ (get grid 0 0 + get grid 0 1 + get grid 1 1)
                   then (1 : ℤ) else 0) +
                  (if (k.val : ℤ) ∣ (get grid 0 0 + get grid 1 0 + get grid 1 1)
                   then (1 : ℤ) else 0) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hm : Rows grid = 2) (hn : Cols grid = 2), ∃ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r ∧
            r.val = (if (k.val : ℤ) ∣ (get grid 0 0 + get grid 0 1 + get grid 1 1)
                     then (1 : ℤ) else 0) +
                    (if (k.val : ℤ) ∣ (get grid 0 0 + get grid 1 0 + get grid 1 1)
                     then (1 : ℤ) else 0)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exists at least one monotone path from (0,0) to (m-1,n-1) moving only down or right whose visited-cell sum is divisible by k.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_13 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) :
      ∀ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r → 0 < r.val →
          existsGoodPath (get grid) (Rows grid) (Cols grid) (kNat k) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k), ∀ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r → 0 < r.val →
            existsGoodPath (get grid) (Rows grid) (Cols grid) (kNat k)) := by
    sorry

  /-- Let N be the number of monotone paths from (0,0) to (m-1,n-1) moving only down or right whose visited-cell sum is divisible by k. Whenever the function returns r = 0, either N = 0 or N is a positive multiple of 1000000007.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_14 (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k) :
      ∀ r : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r → r.val = 0 →
          numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) = 0 ∨
            ∃ c : ℕ, 0 < c ∧
              numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) = MOD * c := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (grid : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k), ∀ r : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r → r.val = 0 →
            numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) = 0 ∨
              ∃ c : ℕ, 0 < c ∧
                numGoodPaths (get grid) (Rows grid) (Cols grid) (kNat k) = MOD * c) := by
    sorry

  /-- For every positive integer c with gcd(c,k) = 1 and such that 0 <= c*grid[i][j] <= 100 for every i,j, let grid' be defined by grid'[i][j] = c*grid[i][j]. If the function returns r on grid and r' on grid', both with the same k, then r = r'.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_15 (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (c : ℕ) (hc : 0 < c) (hgcd : Nat.gcd c (kNat k) = 1)
      (hb : ∀ i j, 0 ≤ (c : ℤ) * get grid i j ∧ (c : ℤ) * get grid i j ≤ 100)
      (h' : Entrywise grid grid' (fun x => (c : ℤ) * x)) :
      ∀ r r' : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r' := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (grid grid' : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (c : ℕ) (hc : 0 < c) (hgcd : Nat.gcd c (kNat k) = 1)
        (hb : ∀ i j, 0 ≤ (c : ℤ) * get grid i j ∧ (c : ℤ) * get grid i j ≤ 100)
        (h' : Entrywise grid grid' (fun x => (c : ℤ) * x)), ∀ r r' : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            Aegis.NumberOfPaths.number_of_paths grid' k = ok r' → r = r') := by
    sorry

  /-- Let gridR be the 180-degree rotation of grid, so gridR[i][j] = grid[m-1-i][n-1-j] for all valid i,j. If the function returns r on grid and rR on gridR, both with the same k, then r = rR.
    Preconditions: Let m = len(grid). The slice is nonempty: m >= 1. Let n = len(grid[0]), so n >= 1. The matrix is rectangular: for every i with 0 <= i < m, len(grid[i]) = n. The dimensions satisfy 1 <= m <= 50000, 1 <= n <= 50000, and m*n <= 50000. Every entry satisfies 0 <= grid[i][j] <= 100 for all 0 <= i < m and 0 <= j < n. Also 1 <= k <= 50. -/
  theorem spec_16 (grid gridR : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
      (hR : IsRot180 grid gridR) :
      ∀ r rR : I64,
        Aegis.NumberOfPaths.number_of_paths grid k = ok r →
          Aegis.NumberOfPaths.number_of_paths gridR k = ok rR → r = rR := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (grid gridR : Slice (alloc.vec.Vec I64)) (k : I64) (h : ValidInput grid k)
        (hR : IsRot180 grid gridR), ∀ r rR : I64,
          Aegis.NumberOfPaths.number_of_paths grid k = ok r →
            Aegis.NumberOfPaths.number_of_paths gridR k = ok rR → r = rR) := by
    sorry

  end AegisSpec.NumberOfPaths
