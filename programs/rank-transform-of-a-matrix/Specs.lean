import Aegis.MatrixRankTransform.Code.Funs

/-!
# Specifications of `Aegis.MatrixRankTransform.matrix_rank_transform`

LeetCode problem `rank-transform-of-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MatrixRankTransform

  open Aegis.MatrixRankTransform (matrix_rank_transform)

  def inList (matrix : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    matrix.val.map fun row => row.val.map fun x => x.val

  def outList (r : alloc.vec.Vec (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    r.val.map fun row => row.val.map fun x => x.val

  def cellAt (A : List (List ℤ)) (i j : ℕ) : ℤ := (A.getD i []).getD j 0

  def entriesInRange (A : List (List ℤ)) : Prop :=
    ∀ row ∈ A, ∀ x ∈ row, -1000000000 ≤ x ∧ x ≤ 1000000000

  def hasShape (A : List (List ℤ)) (m n : ℕ) : Prop :=
    A.length = m ∧ ∀ row ∈ A, row.length = n

  def validInput (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) : Prop :=
    1 ≤ m ∧ 1 ≤ n ∧ hasShape (inList matrix) m n ∧ entriesInRange (inList matrix)

  def preservesRows (A B : List (List ℤ)) (m n : ℕ) : Prop :=
    ∀ i, i < m → ∀ a, a < n → ∀ b, b < n →
      (cellAt A i a < cellAt A i b ↔ cellAt B i a < cellAt B i b) ∧
        (cellAt A i a = cellAt A i b ↔ cellAt B i a = cellAt B i b)

  def preservesCols (A B : List (List ℤ)) (m n : ℕ) : Prop :=
    ∀ j, j < n → ∀ a, a < m → ∀ b, b < m →
      (cellAt A a j < cellAt A b j ↔ cellAt B a j < cellAt B b j) ∧
        (cellAt A a j = cellAt A b j ↔ cellAt B a j = cellAt B b j)

  def isAdmissible (mat S : List (List ℤ)) (m n : ℕ) : Prop :=
    hasShape S m n ∧ (∀ i, i < m → ∀ j, j < n → 1 ≤ cellAt S i j) ∧
      preservesRows mat S m n ∧ preservesCols mat S m n

  def linkStep (mat : List (List ℤ)) (u v : ℕ × ℕ) : Prop :=
    cellAt mat u.1 u.2 = cellAt mat v.1 v.2 ∧ (u.1 = v.1 ∨ u.2 = v.2)

  def linked (mat : List (List ℤ)) (u v : ℕ × ℕ) : Prop :=
    Relation.ReflTransGen (linkStep mat) u v

  def increasingWalk (mat : List (List ℤ)) : List (ℕ × ℕ) → Prop
    | [] => True
    | [_] => True
    | u :: v :: rest =>
      (u.1 = v.1 ∨ u.2 = v.2) ∧ cellAt mat u.1 u.2 < cellAt mat v.1 v.2 ∧
        increasingWalk mat (v :: rest)

  def rankChainWitness (mat : List (List ℤ)) (p : ℕ × ℕ) (L : ℕ) : Prop :=
    ∃ cs : List (ℕ × ℕ), cs.length = L ∧ increasingWalk mat cs ∧
      ∃ last, cs.getLast? = some last ∧ linked mat last p

  def isMinValue (A : List (List ℤ)) (v : ℤ) : Prop :=
    (∀ row ∈ A, ∀ x ∈ row, v ≤ x) ∧ (∃ row ∈ A, ∃ x ∈ row, x = v)

  def isMaxValue (A : List (List ℤ)) (v : ℤ) : Prop :=
    (∀ row ∈ A, ∀ x ∈ row, x ≤ v) ∧ (∃ row ∈ A, ∃ x ∈ row, x = v)

  def numDistinct (A : List (List ℤ)) : ℕ := A.flatten.toFinset.card

  /-- The function returns Ok r, where r is an m x n integer matrix satisfying: (a) r[i][j] >= 1 for all 0 <= i < m and 0 <= j < n; (b) for every row i and columns a,b, matrix[i][a] < matrix[i][b] iff r[i][a] < r[i][b], and matrix[i][a] = matrix[i][b] iff r[i][a] = r[i][b]; (c) for every column j and rows a,b, matrix[a][j] < matrix[b][j] iff r[a][j] < r[b][j], and matrix[a][j] = matrix[b][j] iff r[a][j] = r[b][j]; (d) r is pointwise least among all m x n integer matrices S that satisfy (a), (b), and (c) with r replaced by S, meaning r[i][j] <= S[i][j] for all i,j. This is the complete rank-transform specification.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and -10^9 <= matrix[i][j] <= 10^9 for all 0 <= i < m and 0 <= j < n. The rank-transform answer for matrix is unique, as promised by the problem. -/
  theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
        matrix_rank_transform matrix = ok r ∧
          hasShape (outList r) m n ∧
          (∀ i, i < m → ∀ j, j < n → 1 ≤ cellAt (outList r) i j) ∧
          preservesRows (inList matrix) (outList r) m n ∧
          preservesCols (inList matrix) (outList r) m n ∧
          (∀ S : List (List ℤ), isAdmissible (inList matrix) S m n →
            ∀ i, i < m → ∀ j, j < n → cellAt (outList r) i j ≤ cellAt S i j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
          matrix_rank_transform matrix = ok r ∧
            hasShape (outList r) m n ∧
            (∀ i, i < m → ∀ j, j < n → 1 ≤ cellAt (outList r) i j) ∧
            preservesRows (inList matrix) (outList r) m n ∧
            preservesCols (inList matrix) (outList r) m n ∧
            (∀ S : List (List ℤ), isAdmissible (inList matrix) S m n →
              ∀ i, i < m → ∀ j, j < n → cellAt (outList r) i j ≤ cellAt S i j)) := by
    sorry

  /-- The function returns a result for every valid input: there exists r such that matrix_rank_transform(matrix) = Ok r. It does not fail by overflow, out-of-bounds access, or panic.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and -10^9 <= matrix[i][j] <= 10^9 for all 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) :
      ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), matrix_rank_transform matrix = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64), matrix_rank_transform matrix = ok r) := by
    sorry

  /-- Whenever the function returns Ok r, the result has the same dimensions as the input: len(r) = m, and len(r[i]) = n for every 0 <= i < m.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      (outList r).length = m ∧ ∀ i, i < m → ((outList r).getD i []).length = n := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), (outList r).length = m ∧ ∀ i, i < m → ((outList r).getD i []).length = n) := by
    sorry

  /-- Whenever the function returns Ok r, every entry of r is at least 1: for all 0 <= i < m and 0 <= j < n, r[i][j] >= 1.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ i, i < m → ∀ j, j < n → 1 ≤ cellAt (outList r) i j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ i, i < m → ∀ j, j < n → 1 ≤ cellAt (outList r) i j) := by
    sorry

  /-- Let D be the number of distinct values appearing among all entries of matrix. Whenever the function returns Ok r, every entry of r is at most D: for all i,j, r[i][j] <= D.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ i, i < m → ∀ j, j < n →
        cellAt (outList r) i j ≤ (numDistinct (inList matrix) : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ i, i < m → ∀ j, j < n →
          cellAt (outList r) i j ≤ (numDistinct (inList matrix) : ℤ)) := by
    sorry

  /-- Whenever the function returns Ok r, each row of r preserves the strict order and equality of the corresponding row of matrix: for every row i and every pair of columns a,b, matrix[i][a] < matrix[i][b] iff r[i][a] < r[i][b], and matrix[i][a] = matrix[i][b] iff r[i][a] = r[i][b].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ i, i < m → ∀ a, a < n → ∀ b, b < n →
        (cellAt (inList matrix) i a < cellAt (inList matrix) i b ↔
            cellAt (outList r) i a < cellAt (outList r) i b) ∧
          (cellAt (inList matrix) i a = cellAt (inList matrix) i b ↔
            cellAt (outList r) i a = cellAt (outList r) i b) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ i, i < m → ∀ a, a < n → ∀ b, b < n →
          (cellAt (inList matrix) i a < cellAt (inList matrix) i b ↔
              cellAt (outList r) i a < cellAt (outList r) i b) ∧
            (cellAt (inList matrix) i a = cellAt (inList matrix) i b ↔
              cellAt (outList r) i a = cellAt (outList r) i b)) := by
    sorry

  /-- Whenever the function returns Ok r, each column of r preserves the strict order and equality of the corresponding column of matrix: for every column j and every pair of rows a,b, matrix[a][j] < matrix[b][j] iff r[a][j] < r[b][j], and matrix[a][j] = matrix[b][j] iff r[a][j] = r[b][j].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ j, j < n → ∀ a, a < m → ∀ b, b < m →
        (cellAt (inList matrix) a j < cellAt (inList matrix) b j ↔
            cellAt (outList r) a j < cellAt (outList r) b j) ∧
          (cellAt (inList matrix) a j = cellAt (inList matrix) b j ↔
            cellAt (outList r) a j = cellAt (outList r) b j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ j, j < n → ∀ a, a < m → ∀ b, b < m →
          (cellAt (inList matrix) a j < cellAt (inList matrix) b j ↔
              cellAt (outList r) a j < cellAt (outList r) b j) ∧
            (cellAt (inList matrix) a j = cellAt (inList matrix) b j ↔
              cellAt (outList r) a j = cellAt (outList r) b j)) := by
    sorry

  /-- Whenever the function returns Ok r, r is pointwise minimal among all m x n integer matrices S that have entries at least 1 and preserve the row and column order/equality relations of matrix. That is, for every such S and every i,j, r[i][j] <= S[i][j].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ S : List (List ℤ), isAdmissible (inList matrix) S m n →
        ∀ i, i < m → ∀ j, j < n → cellAt (outList r) i j ≤ cellAt S i j := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ S : List (List ℤ), isAdmissible (inList matrix) S m n →
          ∀ i, i < m → ∀ j, j < n → cellAt (outList r) i j ≤ cellAt S i j) := by
    sorry

  /-- Whenever the function returns Ok r, if two cells are connected by a finite chain of equal matrix values where consecutive cells share a row or a column, then those two cells have equal ranks. Formally, if there are t >= 0 and cells (i_0,j_0),...,(i_t,j_t) with (i_0,j_0)=(i,j), (i_t,j_t)=(k,l), and for every 0 <= s < t, matrix[i_s][j_s] = matrix[i_{s+1}][j_{s+1}] and (i_s = i_{s+1} or j_s = j_{s+1}), then r[i][j] = r[k][l].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_9 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ i, i < m → ∀ j, j < n → ∀ k, k < m → ∀ l, l < n →
        linked (inList matrix) (i, j) (k, l) →
          cellAt (outList r) i j = cellAt (outList r) k l := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ i, i < m → ∀ j, j < n → ∀ k, k < m → ∀ l, l < n →
          linked (inList matrix) (i, j) (k, l) →
            cellAt (outList r) i j = cellAt (outList r) k l) := by
    sorry

  /-- Let vmin be the minimum value among all entries of matrix. Whenever the function returns Ok r, every cell containing vmin has rank 1: for all i,j, if matrix[i][j] = vmin then r[i][j] = 1. In particular, at least one entry of r equals 1.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_10 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (vmin : ℤ) (hvmin : isMinValue (inList matrix) vmin)
      (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      (∀ i, i < m → ∀ j, j < n →
          cellAt (inList matrix) i j = vmin → cellAt (outList r) i j = 1) ∧
        (∃ i, i < m ∧ ∃ j, j < n ∧ cellAt (outList r) i j = 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (vmin : ℤ) (hvmin : isMinValue (inList matrix) vmin)
        (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), (∀ i, i < m → ∀ j, j < n →
            cellAt (inList matrix) i j = vmin → cellAt (outList r) i j = 1) ∧
          (∃ i, i < m ∧ ∃ j, j < n ∧ cellAt (outList r) i j = 1)) := by
    sorry

  /-- Whenever the function returns Ok r, let K be the maximum entry of r. Then every integer from 1 through K occurs as a rank: for every integer k with 1 <= k <= K, there exist i,j such that r[i][j] = k.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row of matrix has length n, and entries are within the stated value range. -/
  theorem spec_11 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) (K : ℤ) (hK : isMaxValue (outList r) K) :
      ∀ k : ℤ, 1 ≤ k → k ≤ K →
        ∃ i, i < m ∧ ∃ j, j < n ∧ cellAt (outList r) i j = k := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r) (K : ℤ) (hK : isMaxValue (outList r) K), ∀ k : ℤ, 1 ≤ k → k ≤ K →
          ∃ i, i < m ∧ ∃ j, j < n ∧ cellAt (outList r) i j = k) := by
    sorry

  /-- Whenever the function returns Ok r for matrix and Ok r' for matrix', we have r = r' (the two results have identical dimensions and entries).
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row has length n, and entries are within the stated value range. Let c be an integer such that matrix'[i][j] = matrix[i][j] + c is also within -10^9 .. 10^9 for every i,j. -/
  theorem spec_12 (matrix matrix' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (c : ℤ)
      (hvalid : validInput matrix m n) (hvalid' : validInput matrix' m n)
      (hshift : ∀ i, i < m → ∀ j, j < n →
        cellAt (inList matrix') i j = cellAt (inList matrix) i j + c)
      (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r)
      (hr' : matrix_rank_transform matrix' = ok r') :
      outList r' = outList r := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (matrix matrix' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (c : ℤ)
        (hvalid : validInput matrix m n) (hvalid' : validInput matrix' m n)
        (hshift : ∀ i, i < m → ∀ j, j < n →
          cellAt (inList matrix') i j = cellAt (inList matrix) i j + c)
        (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r)
        (hr' : matrix_rank_transform matrix' = ok r'), outList r' = outList r) := by
    sorry

  /-- Whenever the function returns Ok r for matrix and Ok rT for MT, the transpose relation holds: for all 0 <= i < m and 0 <= j < n, rT[j][i] = r[i][j].
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row has length n, and entries are within the stated value range. Let MT be the n x m transpose defined by MT[j][i] = matrix[i][j]. -/
  theorem spec_13 (matrix MT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (hvalidT : validInput MT n m)
      (htranspose : ∀ j, j < n → ∀ i, i < m →
        cellAt (inList MT) j i = cellAt (inList matrix) i j)
      (r rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r)
      (hrT : matrix_rank_transform MT = ok rT) :
      ∀ i, i < m → ∀ j, j < n → cellAt (outList rT) j i = cellAt (outList r) i j := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (matrix MT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (hvalidT : validInput MT n m)
        (htranspose : ∀ j, j < n → ∀ i, i < m →
          cellAt (inList MT) j i = cellAt (inList matrix) i j)
        (r rT : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r)
        (hrT : matrix_rank_transform MT = ok rT), ∀ i, i < m → ∀ j, j < n → cellAt (outList rT) j i = cellAt (outList r) i j) := by
    sorry

  /-- Whenever the function returns Ok r for matrix and Ok r' for matrix', we have r'[i][j] = r[p(i)][q(j)] for all 0 <= i < m and 0 <= j < n.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row has length n, and entries are within the stated value range. Let p be a permutation of {0,...,m-1}, q a permutation of {0,...,n-1}, and define matrix' [i][j] = matrix[p(i)][q(j)]. -/
  theorem spec_14 (matrix matrix' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (hvalid' : validInput matrix' m n)
      (p : Fin m → Fin m) (q : Fin n → Fin n)
      (hp : Function.Bijective p) (hq : Function.Bijective q)
      (hperm : ∀ (i : Fin m) (j : Fin n),
        cellAt (inList matrix') i.1 j.1 = cellAt (inList matrix) (p i).1 (q j).1)
      (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r)
      (hr' : matrix_rank_transform matrix' = ok r') :
      ∀ (i : Fin m) (j : Fin n),
        cellAt (outList r') i.1 j.1 = cellAt (outList r) (p i).1 (q j).1 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (matrix matrix' : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (hvalid' : validInput matrix' m n)
        (p : Fin m → Fin m) (q : Fin n → Fin n)
        (hp : Function.Bijective p) (hq : Function.Bijective q)
        (hperm : ∀ (i : Fin m) (j : Fin n),
          cellAt (inList matrix') i.1 j.1 = cellAt (inList matrix) (p i).1 (q j).1)
        (r r' : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r)
        (hr' : matrix_rank_transform matrix' = ok r'), ∀ (i : Fin m) (j : Fin n),
          cellAt (outList r') i.1 j.1 = cellAt (outList r) (p i).1 (q j).1) := by
    sorry

  /-- Whenever the function returns Ok r, for every cell (i,j), let C(i,j) be the set of cells (a,b) reachable from (i,j) by a finite chain in which consecutive cells have equal matrix values and share a row or a column. Then r[i][j] is the largest integer L >= 1 for which there exist cells c_0,...,c_{L-1} such that c_{L-1} is in C(i,j) and, for every 0 <= s < L-1, c_s and c_{s+1} share a row or a column and matrix[c_s] < matrix[c_{s+1}], where matrix[c] denotes the entry of matrix at cell c.
    Preconditions: Let m = len(matrix) and n = len(matrix[0]). The input is valid: 1 <= m,n <= 500, every row has length n, and entries are within the stated value range. -/
  theorem spec_15 (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
      (hr : matrix_rank_transform matrix = ok r) :
      ∀ i, i < m → ∀ j, j < n →
        ∃ L : ℕ, 1 ≤ L ∧ cellAt (outList r) i j = (L : ℤ) ∧
          rankChainWitness (inList matrix) (i, j) L ∧
          (∀ L' : ℕ, rankChainWitness (inList matrix) (i, j) L' → L' ≤ L) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hvalid : validInput matrix m n) (r : alloc.vec.Vec (alloc.vec.Vec Std.I64))
        (hr : matrix_rank_transform matrix = ok r), ∀ i, i < m → ∀ j, j < n →
          ∃ L : ℕ, 1 ≤ L ∧ cellAt (outList r) i j = (L : ℤ) ∧
            rankChainWitness (inList matrix) (i, j) L ∧
            (∀ L' : ℕ, rankChainWitness (inList matrix) (i, j) L' → L' ≤ L)) := by
    sorry

  end AegisSpec.MatrixRankTransform
