import Aegis.MaximumRows.Code.Funs

/-!
# Specifications of `Aegis.MaximumRows.maximum_rows`

LeetCode problem `maximum-rows-covered-by-columns`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumRows

  open Classical

  def rowsOf (matrix : Slice (alloc.vec.Vec I64)) : List (List Int) :=
    matrix.val.map (fun row => row.val)

  def ncols (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
    ((matrix.val[0]?).map (fun row => row.val.length)).getD 0

  def RowCovered (row : List Int) (S : Finset Nat) : Prop :=
    ∀ (j : Nat) (hj : j < row.length), row[j] = 1 → j ∈ S

  noncomputable def coveredCount (rows : List (List Int)) (S : Finset Nat) : Nat :=
    (rows.filter (fun row => RowCovered row S)).length

  noncomputable def columnSets (n k : Nat) : Finset (Finset Nat) :=
    (Finset.range n).powerset.filter (fun S => S.card = k)

  noncomputable def maxCovered (rows : List (List Int)) (n k : Nat) : Nat :=
    (columnSets n k).sup (fun S => coveredCount rows S)

  noncomputable def columnSetsLe (n k : Nat) : Finset (Finset Nat) :=
    (Finset.range n).powerset.filter (fun S => S.card ≤ k)

  noncomputable def maxCoveredLe (rows : List (List Int)) (n k : Nat) : Nat :=
    (columnSetsLe n k).sup (fun S => coveredCount rows S)

  noncomputable def zeroRowCount (rows : List (List Int)) : Nat :=
    (rows.filter (fun row => ∀ x ∈ row, x = 0)).length

  noncomputable def zeroExceptColCount (rows : List (List Int)) (c : Nat) : Nat :=
    (rows.filter (fun row => ∀ (j : Nat) (_hj : j < row.length), j ≠ c → row[j] = 0)).length

  noncomputable def maxZeroExceptColCount (rows : List (List Int)) (n : Nat) : Nat :=
    (Finset.range n).sup (fun c => zeroExceptColCount rows c)

  noncomputable def zeroInColCount (rows : List (List Int)) (c : Nat) : Nat :=
    (rows.filter (fun row => row[c]? = some 0)).length

  noncomputable def maxZeroInColCount (rows : List (List Int)) (n : Nat) : Nat :=
    (Finset.range n).sup (fun c => zeroInColCount rows c)

  noncomputable def rowSumLeCount (rows : List (List Int)) (k : Int) : Nat :=
    (rows.filter (fun row => row.sum ≤ k)).length

  noncomputable def usedCols (rows : List (List Int)) (n : Nat) : Finset Nat :=
    (Finset.range n).filter (fun j => ∃ row ∈ rows, row[j]? = some 1)

  /-- Whenever the function returns a result r, r is the maximum, over all subsets S of the column set {0,...,n-1} with |S| = numSelect, of C(S), where C(S) is the number of rows i with 0 <= i < m such that for every j with 0 <= j < n and matrix[i][j] = 1, the column j belongs to S. Equivalently, r = max_{S subset of {0,...,n-1}, |S| = numSelect} C(S).
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_1 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        r.val = ((maxCovered (rowsOf matrix) n numSelect.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          r.val = ((maxCovered (rowsOf matrix) n numSelect.val.toNat : Nat) : Int)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail (it does not overflow, panic, or access an out-of-bounds index).
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_2 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∃ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∃ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= m.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_3 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        0 ≤ r.val ∧ r.val ≤ (m : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          0 ≤ r.val ∧ r.val ≤ (m : Int)) := by
    sorry

  /-- Let E be the number of rows i with 0 <= i < m such that matrix[i][j] = 0 for every j with 0 <= j < n. Whenever the function returns a result r, r >= E.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_4 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        ((zeroRowCount (rowsOf matrix) : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          ((zeroRowCount (rowsOf matrix) : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every subset S of {0,...,n-1} with |S| = numSelect, C(S) <= r, where C(S) is the number of rows i with 0 <= i < m such that every j with 0 <= j < n and matrix[i][j] = 1 belongs to S.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_5 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        ∀ S : Finset Nat, S ⊆ Finset.range n → S.card = numSelect.val.toNat →
          ((coveredCount (rowsOf matrix) S : Nat) : Int) ≤ r.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          ∀ S : Finset Nat, S ⊆ Finset.range n → S.card = numSelect.val.toNat →
            ((coveredCount (rowsOf matrix) S : Nat) : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a subset S of {0,...,n-1} with |S| = numSelect such that C(S) = r, where C(S) is the number of rows i with 0 <= i < m such that every j with 0 <= j < n and matrix[i][j] = 1 belongs to S.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_6 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        ∃ S : Finset Nat, S ⊆ Finset.range n ∧ S.card = numSelect.val.toNat ∧
          ((coveredCount (rowsOf matrix) S : Nat) : Int) = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          ∃ S : Finset Nat, S ⊆ Finset.range n ∧ S.card = numSelect.val.toNat ∧
            ((coveredCount (rowsOf matrix) S : Nat) : Int) = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = m.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. In addition, matrix[i][j] = 0 for every i with 0 <= i < m and every j with 0 <= j < n. -/
  theorem spec_7 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
      (hzero : ∀ row ∈ rowsOf matrix, ∀ x ∈ row, x = 0) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r → r.val = (m : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
        (hzero : ∀ row ∈ rowsOf matrix, ∀ x ∈ row, x = 0), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r → r.val = (m : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= c < n} Z(c), where Z(c) is the number of rows i with 0 <= i < m such that matrix[i][j] = 0 for every j with 0 <= j < n and j != c.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. In addition, numSelect = 1. -/
  theorem spec_8 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
      (hsel : numSelect.val = 1) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        r.val = ((maxZeroExceptColCount (rowsOf matrix) n : Nat) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
        (hsel : numSelect.val = 1), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          r.val = ((maxZeroExceptColCount (rowsOf matrix) n : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{0 <= c < n} W(c), where W(c) is the number of rows i with 0 <= i < m such that matrix[i][c] = 0.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. In addition, n >= 2 and numSelect = n - 1. -/
  theorem spec_9 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
      (hn_two : 2 ≤ n) (hsel : numSelect.val = (n : Int) - 1) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        r.val = ((maxZeroInColCount (rowsOf matrix) n : Nat) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int))
        (hn_two : 2 ≤ n) (hsel : numSelect.val = (n : Int) - 1), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          r.val = ((maxZeroInColCount (rowsOf matrix) n : Nat) : Int)) := by
    sorry

  /-- Let K be the number of rows i with 0 <= i < m such that the sum, for j from 0 to n-1, of matrix[i][j] is at most numSelect. Whenever the function returns a result r, r <= K.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_10 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        r.val ≤ ((rowSumLeCount (rowsOf matrix) numSelect.val : Nat) : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          r.val ≤ ((rowSumLeCount (rowsOf matrix) numSelect.val : Nat) : Int)) := by
    sorry

  /-- Let A = { j | 0 <= j < n and there exists i with 0 <= i < m and matrix[i][j] = 1 }. Whenever the function returns a result r, r = m if and only if |A| <= numSelect.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_11 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        (r.val = (m : Int) ↔ ((usedCols (rowsOf matrix) n).card : Int) ≤ numSelect.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          (r.val = (m : Int) ↔ ((usedCols (rowsOf matrix) n).card : Int) ≤ numSelect.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = max_{S subset of {0,...,n-1}, |S| <= numSelect} C(S), where C(S) is the number of rows i with 0 <= i < m such that every j with 0 <= j < n and matrix[i][j] = 1 belongs to S.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= numSelect <= n. -/
  theorem spec_12 (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)) :
      ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
        r.val = ((maxCoveredLe (rowsOf matrix) n numSelect.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (numSelect : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hsel_ge : 1 ≤ numSelect.val) (hsel_le : numSelect.val ≤ (n : Int)), ∀ r, Aegis.MaximumRows.maximum_rows matrix numSelect = ok r →
          r.val = ((maxCoveredLe (rowsOf matrix) n numSelect.val.toNat : Nat) : Int)) := by
    sorry

  /-- For two calls on the same matrix with numSelect = k1 and numSelect = k2, if they return results r1 and r2 respectively, then r1 <= r2. Equivalently, the maximum number of covered rows is monotone nondecreasing as numSelect increases.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input satisfies: 1 <= m <= 12; 1 <= n <= 12; for every i with 0 <= i < m, len(matrix[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1; and 1 <= k1 <= k2 <= n. -/
  theorem spec_13 (matrix : Slice (alloc.vec.Vec I64)) (k1 k2 : I64) (m n : Nat)
      (hm : m = matrix.val.length) (hn : n = ncols matrix)
      (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
      (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
      (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
      (hk1_ge : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ (n : Int)) :
      ∀ r1 r2, Aegis.MaximumRows.maximum_rows matrix k1 = ok r1 →
        Aegis.MaximumRows.maximum_rows matrix k2 = ok r2 → r1.val ≤ r2.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (k1 k2 : I64) (m n : Nat)
        (hm : m = matrix.val.length) (hn : n = ncols matrix)
        (hm_ge : 1 ≤ m) (hm_le : m ≤ 12) (hn_ge : 1 ≤ n) (hn_le : n ≤ 12)
        (hrow_len : ∀ row ∈ rowsOf matrix, row.length = n)
        (hrow_entries : ∀ row ∈ rowsOf matrix, ∀ j, j < n → (row[j]? = some 0 ∨ row[j]? = some 1))
        (hk1_ge : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk2_le : k2.val ≤ (n : Int)), ∀ r1 r2, Aegis.MaximumRows.maximum_rows matrix k1 = ok r1 →
          Aegis.MaximumRows.maximum_rows matrix k2 = ok r2 → r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.MaximumRows
