import Aegis.DiagonalSort.Code.Funs

/-!
# Specifications of `Aegis.DiagonalSort.diagonal_sort`

LeetCode problem `sort-the-matrix-diagonally`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DiagonalSort

  def matVals (mat : Slice (alloc.vec.Vec I64)) : List (List ℤ) :=
    mat.val.map (fun row => row.val.map (fun x => x.val))

  def outVals (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List (List ℤ) :=
    r.val.map (fun row => row.val.map (fun x => x.val))

  def cell (M : List (List ℤ)) (i j : ℕ) : ℤ :=
    (M.getD i []).getD j 0

  def rowLens (mat : Slice (alloc.vec.Vec I64)) : List ℕ :=
    mat.val.map (fun row => (alloc.vec.Vec.len row).val)

  def outRowLens (r : alloc.vec.Vec (alloc.vec.Vec I64)) : List ℕ :=
    r.val.map (fun row => (alloc.vec.Vec.len row).val)

  def matCell (mat : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
    cell (matVals mat) i j

  def outCell (r : alloc.vec.Vec (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
    cell (outVals r) i j

  def diagI0 (d : ℤ) : ℕ := (-d).toNat

  def diagJ0 (d : ℤ) : ℕ := d.toNat

  def diagLen (m n : ℕ) (d : ℤ) : ℕ :=
    min (m - diagI0 d) (n - diagJ0 d)

  def diag (M : List (List ℤ)) (m n : ℕ) (d : ℤ) : List ℤ :=
    (List.range (diagLen m n d)).map (fun t => cell M (diagI0 d + t) (diagJ0 d + t))

  def sortedDiag (M : List (List ℤ)) (m n : ℕ) (d : ℤ) : List ℤ :=
    (diag M m n d).mergeSort (fun a b => a ≤ b)

  def DiagsSorted (M : List (List ℤ)) (m n : ℕ) : Prop :=
    ∀ i j, i < m → j < n → i + 1 < m → j + 1 < n → cell M i j ≤ cell M (i + 1) (j + 1)

  def MatrixValid (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) : Prop :=
    (Slice.len mat).val = m ∧
      1 ≤ m ∧ m ≤ 100 ∧
      1 ≤ n ∧ n ≤ 100 ∧
      rowLens mat = List.replicate m n ∧
      (∀ i j, i < m → j < n → 1 ≤ matCell mat i j ∧ matCell mat i j ≤ 100)

  /-- Let m = len(mat) and n be the common row length. The function returns a result r such that len(r) = m, len(r[i]) = n for every i with 0 <= i < m, and for every cell (i, j) with 0 <= i < m and 0 <= j < n the following holds. Set d = j - i, i0 = max(0, -d), j0 = i0 + d (= max(0, d)), and L = min(m - i0, n - j0). Let D be the sequence D[t] = mat[i0 + t][j0 + t] for t = 0, ..., L - 1; these are exactly the values on the diagonal j' - i' = d, listed from top-left to bottom-right. Then r[i][j] equals the element at 0-indexed position (i - i0) of D sorted in non-decreasing order (equivalently, the (i - i0 + 1)-th smallest element of the multiset of D's values).
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∃ r, Aegis.DiagonalSort.diagonal_sort mat = ok r ∧
        (alloc.vec.Vec.len r).val = m ∧
        outRowLens r = List.replicate m n ∧
        (∀ i j, i < m → j < n →
          outCell r i j =
            (sortedDiag (matVals mat) m n ((j : ℤ) - (i : ℤ))).getD
              (i - diagI0 ((j : ℤ) - (i : ℤ))) 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∃ r, Aegis.DiagonalSort.diagonal_sort mat = ok r ∧
          (alloc.vec.Vec.len r).val = m ∧
          outRowLens r = List.replicate m n ∧
          (∀ i j, i < m → j < n →
            outCell r i j =
              (sortedDiag (matVals mat) m n ((j : ℤ) - (i : ℤ))).getD
                (i - diagI0 ((j : ℤ) - (i : ℤ))) 0)) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, r has the same dimensions as mat: len(r) = len(mat), and for every i with 0 <= i < len(mat), len(r[i]) = len(mat[i]). In particular every row of r has length n.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        (alloc.vec.Vec.len r).val = (Slice.len mat).val ∧
          outRowLens r = rowLens mat ∧
          outRowLens r = List.replicate m n := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          (alloc.vec.Vec.len r).val = (Slice.len mat).val ∧
            outRowLens r = rowLens mat ∧
            outRowLens r = List.replicate m n) := by
    sorry

  /-- For every input mat satisfying the preconditions, the function returns a result r; it does not overflow, panic, or fail.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∃ r, Aegis.DiagonalSort.diagonal_sort mat = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∃ r, Aegis.DiagonalSort.diagonal_sort mat = ok r) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, for every i, j with 0 <= i < m, 0 <= j < n, i + 1 < m, and j + 1 < n, we have r[i][j] <= r[i+1][j+1]. That is, adjacent cells along every diagonal of r are non-decreasing from top-left to bottom-right.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ i j, i < m → j < n → i + 1 < m → j + 1 < n →
          outCell r i j ≤ outCell r (i + 1) (j + 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ i j, i < m → j < n → i + 1 < m → j + 1 < n →
            outCell r i j ≤ outCell r (i + 1) (j + 1)) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, for every integer d with -(m - 1) <= d <= n - 1, the multiset of values { r[i][j] : 0 <= i < m, 0 <= j < n, j - i = d } equals the multiset of values { mat[i][j] : 0 <= i < m, 0 <= j < n, j - i = d }.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ d : ℤ, -((m : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
          (diag (outVals r) m n d).Perm (diag (matVals mat) m n d) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ d : ℤ, -((m : ℤ) - 1) ≤ d → d ≤ (n : ℤ) - 1 →
            (diag (outVals r) m n d).Perm (diag (matVals mat) m n d)) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, for every cell (i, j) with 0 <= i < m and 0 <= j < n there exists a cell (i', j') with 0 <= i' < m, 0 <= j' < n such that j' - i' = j - i and mat[i'][j'] = r[i][j].
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ i j, i < m → j < n →
          ∃ i' j', i' < m ∧ j' < n ∧ (j' : ℤ) - (i' : ℤ) = (j : ℤ) - (i : ℤ) ∧
            matCell mat i' j' = outCell r i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ i j, i < m → j < n →
            ∃ i' j', i' < m ∧ j' < n ∧ (j' : ℤ) - (i' : ℤ) = (j : ℤ) - (i : ℤ) ∧
              matCell mat i' j' = outCell r i j) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, every entry of r lies in the input range: for every i, j with 0 <= i < m and 0 <= j < n, 1 <= r[i][j] <= 100.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ i j, i < m → j < n → 1 ≤ outCell r i j ∧ outCell r i j ≤ 100 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ i j, i < m → j < n → 1 ≤ outCell r i j ∧ outCell r i j ≤ 100) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r and len(mat) = 1 (so m = 1), it holds that r[0][j] = mat[0][j] for every j with 0 <= j < n; that is, r = mat.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
      (hm : m = 1) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        (∀ j, j < n → outCell r 0 j = matCell mat 0 j) ∧
          outVals r = matVals mat := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
        (hm : m = 1), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          (∀ j, j < n → outCell r 0 j = matCell mat 0 j) ∧
            outVals r = matVals mat) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r and n = 1 (so every row of mat has length 1), it holds that r[i][0] = mat[i][0] for every i with 0 <= i < m; that is, r = mat.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
      (hn : n = 1) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        (∀ i, i < m → outCell r i 0 = matCell mat i 0) ∧
          outVals r = matVals mat := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
        (hn : n = 1), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          (∀ i, i < m → outCell r i 0 = matCell mat i 0) ∧
            outVals r = matVals mat) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r and the input already has non-decreasing diagonals, i.e. for every i, j with 0 <= i < m, 0 <= j < n, i + 1 < m, and j + 1 < n we have mat[i][j] <= mat[i+1][j+1], it holds that r[i][j] = mat[i][j] for every cell (i, j) with 0 <= i < m and 0 <= j < n; that is, r = mat.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_10 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
      (hs : DiagsSorted (matVals mat) m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        (∀ i j, i < m → j < n → outCell r i j = matCell mat i j) ∧
          outVals r = matVals mat := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n)
        (hs : DiagsSorted (matVals mat) m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          (∀ i j, i < m → j < n → outCell r i j = matCell mat i j) ∧
            outVals r = matVals mat) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, for every cell (i, j) with 0 <= i < m and 0 <= j < n such that i = 0 or j = 0, r[i][j] equals the minimum of the input values on the diagonal j' - i' = j - i, i.e. r[i][j] = min { mat[i'][j'] : 0 <= i' < m, 0 <= j' < n, j' - i' = j - i }.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_11 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ i j, i < m → j < n → (i = 0 ∨ j = 0) →
          (diag (matVals mat) m n ((j : ℤ) - (i : ℤ))).min? = some (outCell r i j) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ i j, i < m → j < n → (i = 0 ∨ j = 0) →
            (diag (matVals mat) m n ((j : ℤ) - (i : ℤ))).min? = some (outCell r i j)) := by
    sorry

  /-- With m = len(mat) and n the common row length, whenever the function returns a result r, for every cell (i, j) with 0 <= i < m and 0 <= j < n such that i = m - 1 or j = n - 1, r[i][j] equals the maximum of the input values on the diagonal j' - i' = j - i, i.e. r[i][j] = max { mat[i'][j'] : 0 <= i' < m, 0 <= j' < n, j' - i' = j - i }.
    Preconditions: mat is a slice of vectors representing an m x n matrix: m = len(mat) with 1 <= m <= 100, and there is an integer n with 1 <= n <= 100 such that for every i with 0 <= i < m, len(mat[i]) = n. For every i, j with 0 <= i < m and 0 <= j < n, 1 <= mat[i][j] <= 100. -/
  theorem spec_12 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n) :
      ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
        ∀ i j, i < m → j < n → (i = m - 1 ∨ j = n - 1) →
          (diag (matVals mat) m n ((j : ℤ) - (i : ℤ))).max? = some (outCell r i j) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ) (h : MatrixValid mat m n), ∀ r, Aegis.DiagonalSort.diagonal_sort mat = ok r →
          ∀ i j, i < m → j < n → (i = m - 1 ∨ j = n - 1) →
            (diag (matVals mat) m n ((j : ℤ) - (i : ℤ))).max? = some (outCell r i j)) := by
    sorry

  end AegisSpec.DiagonalSort
