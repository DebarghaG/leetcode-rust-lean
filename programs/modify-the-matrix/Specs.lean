import Aegis.ModifiedMatrix.Code.Funs

/-!
# Specifications of `Aegis.ModifiedMatrix.modified_matrix`

LeetCode problem `modify-the-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.ModifiedMatrix

  namespace AegisSpec.ModifiedMatrix

  def entryOfRows (rows : List (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    (rows[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

  def entry (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    entryOfRows matrix.val i j

  def outEntry (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    entryOfRows r.val i j

  def IsColMax (rows : List (alloc.vec.Vec Std.I64)) (m j : Nat) (Mx : Int) : Prop :=
    (∀ k x, k < m → entryOfRows rows k j = some x → x ≤ Mx) ∧
      ∃ k, k < m ∧ entryOfRows rows k j = some Mx

  def HasRowLen (matrix : Slice (alloc.vec.Vec Std.I64)) (n : Nat) : Prop :=
    ∀ (i : Nat) (row : alloc.vec.Vec Std.I64), matrix.val[i]? = some row → row.val.length = n

  def HasShape (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    r.val.length = m ∧ ∀ (i : Nat) (row : alloc.vec.Vec Std.I64), r.val[i]? = some row →
      row.val.length = n

  /-- The function returns a result r such that len(r) = m, len(r[i]) = n for every 0 <= i < m, and for every 0 <= i < m and 0 <= j < n: if matrix[i][j] = -1 then r[i][j] = M_j, and otherwise r[i][j] = matrix[i][j].
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_1
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∃ r, modified_matrix matrix = ok r ∧ HasShape r m n ∧
      (∀ i j, i < m → j < n → entry matrix i j = some (-1) → outEntry r i j = some (M j)) ∧
      (∀ i j, i < m → j < n → entry matrix i j ≠ some (-1) →
        outEntry r i j = entry matrix i j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∃ r, modified_matrix matrix = ok r ∧ HasShape r m n ∧
        (∀ i j, i < m → j < n → entry matrix i j = some (-1) → outEntry r i j = some (M j)) ∧
        (∀ i j, i < m → j < n → entry matrix i j ≠ some (-1) →
          outEntry r i j = entry matrix i j)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or perform an out-of-bounds access.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_2
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∃ r, modified_matrix matrix = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∃ r, modified_matrix matrix = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r has exactly the same shape as matrix: len(r) = m and len(r[i]) = n for every 0 <= i < m.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_3
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → HasShape r m n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → HasShape r m n) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n with matrix[i][j] != -1, we have r[i][j] = matrix[i][j].
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_4
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j ≠ some (-1) →
      outEntry r i j = entry matrix i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j ≠ some (-1) →
        outEntry r i j = entry matrix i j) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n with matrix[i][j] = -1, we have r[i][j] = M_j.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_5
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
      outEntry r i j = some (M j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
        outEntry r i j = some (M j)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n with matrix[i][j] = -1, and for every 0 <= k < m, we have r[i][j] >= matrix[k][j].
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_6
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
      ∀ k x, k < m → entry matrix k j = some x → ∃ y, outEntry r i j = some y ∧ x ≤ y := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
        ∀ k x, k < m → entry matrix k j = some x → ∃ y, outEntry r i j = some y ∧ x ≤ y) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n with matrix[i][j] = -1, there exists 0 <= k < m such that r[i][j] = matrix[k][j].
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_7
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
      ∃ k x, k < m ∧ entry matrix k j = some x ∧ outEntry r i j = some x := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n → entry matrix i j = some (-1) →
        ∃ k x, k < m ∧ entry matrix k j = some x ∧ outEntry r i j = some x) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, we have -1 <= r[i][j] <= 100.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_8
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n →
      ∃ x, outEntry r i j = some x ∧ -1 ≤ x ∧ x ≤ 100 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n →
        ∃ x, outEntry r i j = some x ∧ -1 ≤ x ∧ x ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= j < n and all 0 <= i < m and 0 <= i' < m, if matrix[i][j] = -1 and matrix[i'][j] = -1, then r[i][j] = r[i'][j].
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_9
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ j i i', j < n → i < m → i' < m →
      entry matrix i j = some (-1) → entry matrix i' j = some (-1) →
      outEntry r i j = outEntry r i' j := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ j i i', j < n → i < m → i' < m →
        entry matrix i j = some (-1) → entry matrix i' j = some (-1) →
        outEntry r i j = outEntry r i' j) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= j < n, the maximum of the output column j is still M_j: that is, r[k][j] <= M_j for every 0 <= k < m, and r[k0][j] = M_j for some 0 <= k0 < m.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_10
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ j, j < n → IsColMax r.val m j (M j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ j, j < n → IsColMax r.val m j (M j)) := by
    sorry

  /-- Whenever the function returns a result r, for every 0 <= i < m and 0 <= j < n, we have 0 <= r[i][j] <= 100.
    Preconditions: Let m = len(matrix). Assume 2 <= m <= 50. Let n = len(matrix[0]) (well-defined because m >= 2). Assume 2 <= n <= 50, and len(matrix[i]) = n for every 0 <= i < m. Assume -1 <= matrix[i][j] <= 100 for every 0 <= i < m and 0 <= j < n, and that for every 0 <= j < n there exists 0 <= i < m with matrix[i][j] >= 0. For each 0 <= j < n, let M_j be the maximum of column j: the unique integer such that matrix[k][j] <= M_j for every 0 <= k < m and M_j = matrix[k0][j] for some 0 <= k0 < m. -/
  theorem spec_11
    (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
    (hm : matrix.val.length = m)
    (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
    (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
    (hrows : HasRowLen matrix n)
    (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
    (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
    (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)) :
    ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n →
      ∃ x, outEntry r i j = some x ∧ 0 ≤ x ∧ x ≤ 100 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) (M : Nat → Int)
      (hm : matrix.val.length = m)
      (hm2 : 2 ≤ m) (hm50 : m ≤ 50)
      (hn2 : 2 ≤ n) (hn50 : n ≤ 50)
      (hrows : HasRowLen matrix n)
      (hentries : ∀ i j x, i < m → j < n → entry matrix i j = some x → -1 ≤ x ∧ x ≤ 100)
      (hcol : ∀ j, j < n → ∃ i x, i < m ∧ entry matrix i j = some x ∧ 0 ≤ x)
      (hmax : ∀ j, j < n → IsColMax matrix.val m j (M j)), ∀ r, modified_matrix matrix = ok r → ∀ i j, i < m → j < n →
        ∃ x, outEntry r i j = some x ∧ 0 ≤ x ∧ x ≤ 100) := by
    sorry

  end AegisSpec.ModifiedMatrix
