import Aegis.MaxMatrixSum.Code.Funs

/-!
# Specifications of `Aegis.MaxMatrixSum.max_matrix_sum`

LeetCode problem `maximum-matrix-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MaxMatrixSum

  namespace AegisSpec.MaxMatrixSum

  def entries (matrix : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    matrix.val.flatMap (fun row => row.val.map (fun x => x.val))

  def dim (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ := matrix.val.length

  def get (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    ((matrix.val[i]?).bind (fun row => row.val[j]?)).map (fun x => x.val) |>.getD 0

  def rowLen (matrix : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    (matrix.val[i]?).map (fun row => row.val.length) |>.getD 0

  def listMin : List ℤ → ℤ
    | [] => 0
    | a :: t => t.foldr min a

  def sumAbs (matrix : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (entries matrix).map (fun x => |x|) |>.sum

  def sumVal (matrix : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (entries matrix).sum

  def negCount (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    ((entries matrix).filter (fun x => x < 0)).length

  def minAbs (matrix : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    listMin ((entries matrix).map (fun x => |x|))

  def Valid (matrix : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    2 ≤ dim matrix ∧ dim matrix ≤ 250 ∧
      (∀ i, i < dim matrix → rowLen matrix i = dim matrix) ∧
      (∀ i j, i < dim matrix → j < dim matrix →
        -100000 ≤ get matrix i j ∧ get matrix i j ≤ 100000)

  def HasZero (matrix : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ i, i < dim matrix ∧ ∃ j, j < dim matrix ∧ get matrix i j = 0

  def AllNonneg (matrix : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i j, i < dim matrix → j < dim matrix → 0 ≤ get matrix i j

  def AllZero (matrix : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∀ i j, i < dim matrix → j < dim matrix → get matrix i j = 0

  def IsSignMatrix (matrix : Slice (alloc.vec.Vec Std.I64)) (s : ℕ → ℕ → ℤ) : Prop :=
    ∀ i j, i < dim matrix → j < dim matrix → s i j = 1 ∨ s i j = -1

  def signSum (matrix : Slice (alloc.vec.Vec Std.I64)) (s : ℕ → ℕ → ℤ) : ℤ :=
    (Finset.range (dim matrix)).sum
      (fun i => (Finset.range (dim matrix)).sum (fun j => s i j * get matrix i j))

  def signProd (matrix : Slice (alloc.vec.Vec Std.I64)) (s : ℕ → ℕ → ℤ) : ℤ :=
    (Finset.range (dim matrix)).prod
      (fun i => (Finset.range (dim matrix)).prod (fun j => s i j))

  def scaleEntry (k : ℤ) (x : Std.I64) : Std.I64 :=
    ⟨BitVec.ofInt 64 (k * x.val)⟩

  def scaleVec (k : ℤ) (row : alloc.vec.Vec Std.I64) : alloc.vec.Vec Std.I64 :=
    ⟨{ leng := (row.val.map (scaleEntry k)).length
       list := Aeneas.Data.ListN.ListN.fromList (row.val.map (scaleEntry k))
       bound := by
         rw [List.length_map]
         show (row.slice.list.toList).length ≤ Usize.max
         rw [Aeneas.Data.ListN.ListN_length]
         exact row.slice.bound }⟩

  def scale (k : ℤ) (matrix : Slice (alloc.vec.Vec Std.I64)) : Slice (alloc.vec.Vec Std.I64) :=
    { leng := (matrix.val.map (scaleVec k)).length
      list := Aeneas.Data.ListN.ListN.fromList (matrix.val.map (scaleVec k))
      bound := by
        rw [List.length_map]
        show (matrix.list.toList).length ≤ Usize.max
        rw [Aeneas.Data.ListN.ListN_length]
        exact matrix.bound }

  /-- The function returns a result r, and r = sum_abs(matrix) if neg_count(matrix) is even, while r = sum_abs(matrix) - 2 * min_abs(matrix) if neg_count(matrix) is odd. Here sum_abs(matrix) is the sum of |matrix[i][j]| over all 0 <= i < n and 0 <= j < n; neg_count(matrix) is the number of pairs (i,j) with matrix[i][j] < 0; min_abs(matrix) is the minimum of |matrix[i][j]| over all 0 <= i < n and 0 <= j < n.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∃ x : Std.I64, max_matrix_sum matrix = ok x ∧
        (x.val = if Even (negCount matrix) then sumAbs matrix
                 else sumAbs matrix - 2 * minAbs matrix) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∃ x : Std.I64, max_matrix_sum matrix = ok x ∧
          (x.val = if Even (negCount matrix) then sumAbs matrix
                   else sumAbs matrix - 2 * minAbs matrix)) := by
    sorry

  /-- The function returns a result r and 0 <= r <= 6250000000.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∃ x : Std.I64, max_matrix_sum matrix = ok x ∧ 0 ≤ x.val ∧ x.val ≤ 6250000000 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∃ x : Std.I64, max_matrix_sum matrix = ok x ∧ 0 ≤ x.val ∧ x.val ≤ 6250000000) := by
    sorry

  /-- Whenever the function returns a result r, r <= sum_abs(matrix), where sum_abs(matrix) = Σ_{0 <= i < n, 0 <= j < n} |matrix[i][j]|.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → x.val ≤ sumAbs matrix := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → x.val ≤ sumAbs matrix) := by
    sorry

  /-- Whenever the function returns a result r, r >= Σ_{0 <= i < n, 0 <= j < n} matrix[i][j].
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → sumVal matrix ≤ x.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → sumVal matrix ≤ x.val) := by
    sorry

  /-- Whenever the function returns a result r, if there exist i,j with 0 <= i < n and 0 <= j < n and matrix[i][j] = 0, then r = sum_abs(matrix), where sum_abs(matrix) = Σ_{0 <= i < n, 0 <= j < n} |matrix[i][j]|.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → HasZero matrix → x.val = sumAbs matrix := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → HasZero matrix → x.val = sumAbs matrix) := by
    sorry

  /-- Whenever the function returns a result r, if matrix[i][j] >= 0 for every 0 <= i < n and 0 <= j < n, then r = Σ_{0 <= i < n, 0 <= j < n} matrix[i][j].
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → AllNonneg matrix → x.val = sumVal matrix := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → AllNonneg matrix → x.val = sumVal matrix) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if matrix[i][j] = 0 for every 0 <= i < n and 0 <= j < n.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → (x.val = 0 ↔ AllZero matrix) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → (x.val = 0 ↔ AllZero matrix)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_abs(matrix) if and only if neg_count(matrix) is even or there exist i,j with 0 <= i < n and 0 <= j < n and matrix[i][j] = 0. Here sum_abs(matrix) = Σ_{0 <= i < n, 0 <= j < n} |matrix[i][j]| and neg_count(matrix) is the number of entries of matrix that are strictly negative.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x →
        (x.val = sumAbs matrix ↔ Even (negCount matrix) ∨ HasZero matrix) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x →
          (x.val = sumAbs matrix ↔ Even (negCount matrix) ∨ HasZero matrix)) := by
    sorry

  /-- Whenever the function returns a result r, r - Σ_{0 <= i < n, 0 <= j < n} matrix[i][j] is even.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_9 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x → Even (x.val - sumVal matrix) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x → Even (x.val - sumVal matrix)) := by
    sorry

  /-- If |B[i][j]| = |matrix[i][j]| for every 0 <= i < n and 0 <= j < n and neg_count(B) and neg_count(matrix) have the same parity, then the value returned for B equals the value returned for matrix. Here neg_count(M) is the number of entries of M that are strictly negative.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. Let B be an n x n integer matrix with -100000 <= B[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_10 (matrix B : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) (hB : Valid B)
      (hlen : dim B = dim matrix)
      (habs : ∀ i j, i < dim matrix → j < dim matrix → |get B i j| = |get matrix i j|)
      (hpar : negCount B % 2 = negCount matrix % 2) :
      ∀ xB xM : Std.I64, max_matrix_sum B = ok xB → max_matrix_sum matrix = ok xM →
        xB.val = xM.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix B : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) (hB : Valid B)
        (hlen : dim B = dim matrix)
        (habs : ∀ i j, i < dim matrix → j < dim matrix → |get B i j| = |get matrix i j|)
        (hpar : negCount B % 2 = negCount matrix % 2), ∀ xB xM : Std.I64, max_matrix_sum B = ok xB → max_matrix_sum matrix = ok xM →
          xB.val = xM.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist signs s[i][j] ∈ {+1, -1} for 0 <= i < n and 0 <= j < n such that the product of all n^2 signs s[i][j] is +1 and r = Σ_{0 <= i < n, 0 <= j < n} s[i][j] * matrix[i][j].
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_11 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x →
        ∃ s : ℕ → ℕ → ℤ,
          IsSignMatrix matrix s ∧ signProd matrix s = 1 ∧ x.val = signSum matrix s := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x →
          ∃ s : ℕ → ℕ → ℤ,
            IsSignMatrix matrix s ∧ signProd matrix s = 1 ∧ x.val = signSum matrix s) := by
    sorry

  /-- Whenever the function returns a result r, for every choice of signs s[i][j] ∈ {+1, -1} for 0 <= i < n and 0 <= j < n with product +1, we have Σ_{0 <= i < n, 0 <= j < n} s[i][j] * matrix[i][j] <= r.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_12 (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix) :
      ∀ x : Std.I64, max_matrix_sum matrix = ok x →
        ∀ s : ℕ → ℕ → ℤ,
          IsSignMatrix matrix s → signProd matrix s = 1 → signSum matrix s ≤ x.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (h : Valid matrix), ∀ x : Std.I64, max_matrix_sum matrix = ok x →
          ∀ s : ℕ → ℕ → ℤ,
            IsSignMatrix matrix s → signProd matrix s = 1 → signSum matrix s ≤ x.val) := by
    sorry

  /-- The value returned for the matrix whose (i,j) entry is k * matrix[i][j] equals k times the value returned for matrix.
    Preconditions: Let n = len(matrix). The input satisfies 2 <= n <= 250, len(matrix[i]) = n for every 0 <= i < n, and -100000 <= matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. Let k be an integer with 0 <= k <= 100000 such that -100000 <= k * matrix[i][j] <= 100000 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_13 (matrix : Slice (alloc.vec.Vec Std.I64)) (k : ℤ) (h : Valid matrix)
      (hk0 : 0 ≤ k) (hk1 : k ≤ 100000)
      (hkbound : ∀ i j, i < dim matrix → j < dim matrix →
        -100000 ≤ k * get matrix i j ∧ k * get matrix i j ≤ 100000) :
      ∀ xM xK : Std.I64, max_matrix_sum matrix = ok xM →
        max_matrix_sum (scale k matrix) = ok xK → xK.val = k * xM.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (k : ℤ) (h : Valid matrix)
        (hk0 : 0 ≤ k) (hk1 : k ≤ 100000)
        (hkbound : ∀ i j, i < dim matrix → j < dim matrix →
          -100000 ≤ k * get matrix i j ∧ k * get matrix i j ≤ 100000), ∀ xM xK : Std.I64, max_matrix_sum matrix = ok xM →
          max_matrix_sum (scale k matrix) = ok xK → xK.val = k * xM.val) := by
    sorry

  end AegisSpec.MaxMatrixSum
