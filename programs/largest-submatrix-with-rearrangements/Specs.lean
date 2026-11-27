import Aegis.LargestSubmatrix.Code.Funs

/-!
# Specifications of `Aegis.LargestSubmatrix.largest_submatrix`

LeetCode problem `largest-submatrix-with-rearrangements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical
open Aegis.LargestSubmatrix

namespace AegisSpec.LargestSubmatrix

def nrows (matrix : Slice (alloc.vec.Vec I64)) : Nat := matrix.val.length

def ncols (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  match matrix.val with
  | [] => 0
  | row :: _ => row.val.length

def rowLen (matrix : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat :=
  match matrix.val[i]? with
  | none => 0
  | some row => row.val.length

def cell (matrix : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match matrix.val[i]? with
  | none => 0
  | some row => ((row.val[j]?).map (fun v => v.val)).getD 0

def ColOnes (matrix : Slice (alloc.vec.Vec I64)) (a b c : Nat) : Prop :=
  ∀ i, a ≤ i → i ≤ b → cell matrix i c = 1

def intervals (matrix : Slice (alloc.vec.Vec I64)) : Finset (Nat × Nat) :=
  Finset.filter (fun p : Nat × Nat => p.1 ≤ p.2)
    (Finset.product (Finset.range (nrows matrix)) (Finset.range (nrows matrix)))

noncomputable def W (matrix : Slice (alloc.vec.Vec I64)) (a b : Nat) : Nat :=
  (Finset.filter (fun c => ColOnes matrix a b c) (Finset.range (ncols matrix))).card

noncomputable def maxArea (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  Finset.sup (intervals matrix) (fun p => (p.2 - p.1 + 1) * W matrix p.1 p.2)

noncomputable def colRun (matrix : Slice (alloc.vec.Vec I64)) (c : Nat) : Nat :=
  Finset.sup (Finset.filter (fun p : Nat × Nat => ColOnes matrix p.1 p.2 c) (intervals matrix))
    (fun p => p.2 - p.1 + 1)

noncomputable def maxColRun (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  Finset.sup (Finset.range (ncols matrix)) (fun c => colRun matrix c)

noncomputable def rowOnes (matrix : Slice (alloc.vec.Vec I64)) (i : Nat) : Nat :=
  (Finset.filter (fun j => cell matrix i j = 1) (Finset.range (ncols matrix))).card

noncomputable def maxRowOnes (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  Finset.sup (Finset.range (nrows matrix)) (fun i => rowOnes matrix i)

noncomputable def totalOnes (matrix : Slice (alloc.vec.Vec I64)) : Nat :=
  (Finset.filter (fun p : Nat × Nat => cell matrix p.1 p.2 = 1)
    (Finset.product (Finset.range (nrows matrix)) (Finset.range (ncols matrix)))).card

def IsColPerm (matrix matrix' : Slice (alloc.vec.Vec I64))
    (p : Equiv.Perm (Fin (ncols matrix))) : Prop :=
  nrows matrix' = nrows matrix ∧ ncols matrix' = ncols matrix ∧
    (∀ i, i < nrows matrix' → rowLen matrix' i = ncols matrix') ∧
    ∀ (i j : Nat), i < nrows matrix → ∀ (hj : j < ncols matrix),
      cell matrix' i j = cell matrix i (p ⟨j, hj⟩).val

/-- The function returns a result r, and r equals the maximum, over all pairs (a,b) with 0 <= a <= b < m, of (b-a+1) * W(a,b), where W(a,b) is the number of column indices c with 0 <= c < n such that matrix[i][c] = 1 for every i with a <= i <= b. If all these areas are 0, then r = 0.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1) :
    ∃ r, largest_submatrix matrix = ok r ∧ r.val = (maxArea matrix : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1), ∃ r, largest_submatrix matrix = ok r ∧ r.val = (maxArea matrix : Int)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, or overflow.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1) :
    ∃ r, largest_submatrix matrix = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1), ∃ r, largest_submatrix matrix = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= m*n.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((nrows matrix * ncols matrix : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), 0 ≤ r.val ∧ r.val ≤ ((nrows matrix * ncols matrix : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= T, where T is the total number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = 1.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val ≤ (totalOnes matrix : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val ≤ (totalOnes matrix : Int)) := by
  sorry

/-- Whenever the function returns a result r and r > 0, there exist integers a,b and a finite set S of column indices such that 0 <= a <= b < m, S is a subset of {0,1,...,n-1}, (b-a+1) * |S| = r, and matrix[i][c] = 1 for every i with a <= i <= b and every c in S.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) (hrpos : 0 < r.val) :
    ∃ (a b : Nat) (S : Finset Nat),
      a ≤ b ∧ b < nrows matrix ∧ (∀ c ∈ S, c < ncols matrix) ∧
      (((b - a + 1) * S.card : Nat) : Int) = r.val ∧
      (∀ i, a ≤ i → i ≤ b → ∀ c ∈ S, cell matrix i c = 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) (hrpos : 0 < r.val), ∃ (a b : Nat) (S : Finset Nat),
      a ≤ b ∧ b < nrows matrix ∧ (∀ c ∈ S, c < ncols matrix) ∧
      (((b - a + 1) * S.card : Nat) : Int) = r.val ∧
      (∀ i, a ≤ i → i ≤ b → ∀ c ∈ S, cell matrix i c = 1)) := by
  sorry

/-- Whenever the function returns a result r, for every pair a,b with 0 <= a <= b < m and every finite set S of column indices with S subset of {0,1,...,n-1} and matrix[i][c] = 1 for all i with a <= i <= b and all c in S, we have (b-a+1) * |S| <= r.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    ∀ (a b : Nat) (S : Finset Nat),
      a ≤ b → b < nrows matrix → (∀ c ∈ S, c < ncols matrix) →
      (∀ i, a ≤ i → i ≤ b → ∀ c ∈ S, cell matrix i c = 1) →
      (((b - a + 1) * S.card : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), ∀ (a b : Nat) (S : Finset Nat),
      a ≤ b → b < nrows matrix → (∀ c ∈ S, c < ncols matrix) →
      (∀ i, a ≤ i → i ≤ b → ∀ c ∈ S, cell matrix i c = 1) →
      (((b - a + 1) * S.card : Nat) : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if matrix[i][j] = 0 for every i with 0 <= i < m and every j with 0 <= j < n.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    (r.val = 0 ↔ ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = 0) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), (r.val = 0 ↔ ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = 0)) := by
  sorry

/-- Whenever the function returns a result r, r = m*n.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. Assume additionally that matrix[i][j] = 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_8 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hall : ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val = ((nrows matrix * ncols matrix : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hall : ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val = ((nrows matrix * ncols matrix : Nat) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r equals the number of j with 0 <= j < n and matrix[0][j] = 1.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. Assume additionally that m = 1. -/
theorem spec_9 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hm1 : nrows matrix = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val = (rowOnes matrix 0 : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hm1 : nrows matrix = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val = (rowOnes matrix 0 : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is the maximum length b-a+1 over all intervals 0 <= a <= b < m such that matrix[i][0] = 1 for every i with a <= i <= b; if there is no such interval, then r = 0.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. Assume additionally that n = 1. -/
theorem spec_10 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hn1 : ncols matrix = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val = (maxColRun matrix : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hn1 : ncols matrix = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val = (maxColRun matrix : Int)) := by
  sorry

/-- For every permutation p of {0,1,...,n-1}, let matrix' be the m x n matrix defined by matrix'[i][j] = matrix[i][p(j)] for all 0 <= i < m and 0 <= j < n. Whenever the function returns r on matrix and r' on matrix', we have r = r'.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_11 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (p : Equiv.Perm (Fin (ncols matrix))) (matrix' : Slice (alloc.vec.Vec I64))
    (hperm : IsColPerm matrix matrix' p)
    (r r' : I64)
    (hr : largest_submatrix matrix = ok r) (hr' : largest_submatrix matrix' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (p : Equiv.Perm (Fin (ncols matrix))) (matrix' : Slice (alloc.vec.Vec I64))
    (hperm : IsColPerm matrix matrix' p)
    (r r' : I64)
    (hr : largest_submatrix matrix = ok r) (hr' : largest_submatrix matrix' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r = m * K, where K is the number of j with 0 <= j < n and matrix[0][j] = 1.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. Assume additionally that all rows of matrix are identical. -/
theorem spec_12 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hid : ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = cell matrix 0 j)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val = ((nrows matrix * rowOnes matrix 0 : Nat) : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (hid : ∀ i j, i < nrows matrix → j < ncols matrix → cell matrix i j = cell matrix 0 j)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val = ((nrows matrix * rowOnes matrix 0 : Nat) : Int)) := by
  sorry

/-- Let L be the maximum of b-a+1 over all triples (a,b,c) such that 0 <= c < n, 0 <= a <= b < m, and matrix[i][c] = 1 for every i with a <= i <= b; if no such triple exists, let L = 0. Whenever the function returns a result r, r >= L.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    (maxColRun matrix : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), (maxColRun matrix : Int) ≤ r.val) := by
  sorry

/-- Let R be the maximum, over rows i with 0 <= i < m, of the number of j with 0 <= j < n and matrix[i][j] = 1. Whenever the function returns a result r, r >= R.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_14 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    (maxRowOnes matrix : Int) ≤ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), (maxRowOnes matrix : Int) ≤ r.val) := by
  sorry

/-- Let L be the maximum length of a contiguous run of 1s in any single column, or 0 if no such run exists: L is the maximum of b-a+1 over all triples (a,b,c) with 0 <= c < n, 0 <= a <= b < m, and matrix[i][c] = 1 for every i with a <= i <= b, or L = 0 if there is no such triple. Whenever the function returns a result r, r <= n * L.
  Preconditions: Let m = len(matrix) and n = len(matrix[0]). Assume m >= 1, n >= 1, m*n <= 100000, every row of matrix has length n, and matrix[i][j] is either 0 or 1 for all 0 <= i < m and 0 <= j < n. -/
theorem spec_15 (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r) :
    r.val ≤ ((ncols matrix * maxColRun matrix : Nat) : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64))
    (hm : 1 ≤ nrows matrix) (hn : 1 ≤ ncols matrix)
    (hsize : nrows matrix * ncols matrix ≤ 100000)
    (hrows : ∀ i, i < nrows matrix → rowLen matrix i = ncols matrix)
    (hbin : ∀ i j, i < nrows matrix → j < ncols matrix →
      cell matrix i j = 0 ∨ cell matrix i j = 1)
    (r : I64) (hr : largest_submatrix matrix = ok r), r.val ≤ ((ncols matrix * maxColRun matrix : Nat) : Int)) := by
  sorry

end AegisSpec.LargestSubmatrix
