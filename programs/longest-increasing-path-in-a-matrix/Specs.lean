import Aegis.LongestIncreasingPath.Code.Funs

/-!
# Specifications of `Aegis.LongestIncreasingPath.longest_increasing_path`

LeetCode problem `longest-increasing-path-in-a-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.LongestIncreasingPath

def mrows (matrix : Slice (alloc.vec.Vec I64)) : List (List Int) :=
  matrix.val.map fun row => row.val.map fun x => x.val

def cell (matrix : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
  match matrix.val[i]? with
  | some row => ((row.val[j]?).map fun x => x.val).getD 0
  | none => 0

def ValidMatrix (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat) : Prop :=
  matrix.val.length = m ∧
  1 ≤ m ∧
  1 ≤ n ∧ n ≤ 200 ∧ m ≤ 200 ∧
  (∀ row ∈ matrix.val, row.val.length = n) ∧
  (∀ row ∈ matrix.val, ∀ x ∈ row.val, 0 ≤ x.val ∧ x.val ≤ 2147483647)

def manhattan (p q : Nat × Nat) : Nat :=
  (p.1 - q.1) + (q.1 - p.1) + (p.2 - q.2) + (q.2 - p.2)

def OrthAdjacent (p q : Nat × Nat) : Prop := manhattan p q = 1

def PathStepsOK (matrix : Slice (alloc.vec.Vec I64)) (path : List (Nat × Nat)) : Prop :=
  ∀ (t : Nat) (p q : Nat × Nat), path[t]? = some p → path[t + 1]? = some q →
    OrthAdjacent p q ∧ cell matrix p.1 p.2 < cell matrix q.1 q.2

def IsIncreasingPath (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (path : List (Nat × Nat)) : Prop :=
  (∀ p ∈ path, p.1 < m ∧ p.2 < n) ∧ PathStepsOK matrix path

def RowIncreasing (matrix : Slice (alloc.vec.Vec I64)) (s k : Nat) : Prop :=
  ∀ t : Nat, t + 1 < k → cell matrix 0 (s + t) < cell matrix 0 (s + t + 1)

def RowDecreasing (matrix : Slice (alloc.vec.Vec I64)) (s k : Nat) : Prop :=
  ∀ t : Nat, t + 1 < k → cell matrix 0 (s + t) > cell matrix 0 (s + t + 1)

def ColIncreasing (matrix : Slice (alloc.vec.Vec I64)) (s k : Nat) : Prop :=
  ∀ t : Nat, t + 1 < k → cell matrix (s + t) 0 < cell matrix (s + t + 1) 0

def ColDecreasing (matrix : Slice (alloc.vec.Vec I64)) (s k : Nat) : Prop :=
  ∀ t : Nat, t + 1 < k → cell matrix (s + t) 0 > cell matrix (s + t + 1) 0

def transposeRows (a : List (List Int)) (n : Nat) : List (List Int) :=
  (List.range n).map fun j => a.map fun row => row.getD j 0

/-- The function returns a result r and r is the maximum length of an increasing path in matrix. Formally, a cell is a pair (i,j) with 0 <= i < m and 0 <= j < n. An increasing path of length k >= 1 is a sequence of cells (i_0,j_0),...,(i_{k-1},j_{k-1}) such that every listed cell is in bounds and, for every t with 0 <= t < k-1, |i_{t+1}-i_t| + |j_{t+1}-j_t| = 1 and matrix[i_t][j_t] < matrix[i_{t+1}][j_{t+1}]. Then r = max { k | there exists an increasing path of length k }.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_1 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∃ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r ∧
      (∃ path : List (Nat × Nat),
        IsIncreasingPath matrix m n path ∧ (path.length : Int) = r.val) ∧
      (∀ path : List (Nat × Nat),
        IsIncreasingPath matrix m n path → (path.length : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∃ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r ∧
      (∃ path : List (Nat × Nat),
        IsIncreasingPath matrix m n path ∧ (path.length : Int) = r.val) ∧
      (∀ path : List (Nat × Nat),
        IsIncreasingPath matrix m n path → (path.length : Int) ≤ r.val)) := by
  sorry

/-- The function returns a result r (it does not fail) for every valid input.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_2 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∃ r : I64, Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∃ r : I64, Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r) := by
  sorry

/-- Whenever the function returns a result r, 1 <= r.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_3 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∀ r : I64, Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∀ r : I64, Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= m * n.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_4 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        r.val ≤ (m : Int) * (n : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        r.val ≤ (m : Int) * (n : Int)) := by
  sorry

/-- Whenever the function returns a result r, there exists an increasing path in matrix of length r, where an increasing path of length k is a sequence of k in-bounds cells whose consecutive cells are orthogonally adjacent and whose matrix values are strictly increasing along the sequence.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_5 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        ∃ path : List (Nat × Nat),
          IsIncreasingPath matrix m n path ∧ (path.length : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        ∃ path : List (Nat × Nat),
          IsIncreasingPath matrix m n path ∧ (path.length : Int) = r.val) := by
  sorry

/-- Whenever the function returns a result r, every increasing path in matrix has length at most r; equivalently, for every k such that there exists an increasing path of length k, k <= r.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        ∀ path : List (Nat × Nat),
          IsIncreasingPath matrix m n path → (path.length : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        ∀ path : List (Nat × Nat),
          IsIncreasingPath matrix m n path → (path.length : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = 1 if and only if matrix[i][j] = matrix[i'][j'] for every i,i',j,j' with 0 <= i < m, 0 <= i' < m, 0 <= j < n, and 0 <= j' < n.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_7 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (r.val = 1 ↔
          ∀ (i i' j j' : Nat), i < m → i' < m → j < n → j' < n →
            cell matrix i j = cell matrix i' j') := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (r.val = 1 ↔
          ∀ (i i' j j' : Nat), i < m → i' < m → j < n → j' < n →
            cell matrix i j = cell matrix i' j')) := by
  sorry

/-- Whenever the function returns a result r and m = 1, r is the maximum k >= 1 for which there exists an integer s with 0 <= s and s + k <= n such that either (for every t with 0 <= t < k-1, matrix[0][s+t] < matrix[0][s+t+1]) or (for every t with 0 <= t < k-1, matrix[0][s+t] > matrix[0][s+t+1]).
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. Also m = 1. -/
theorem spec_8 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) (hm : m = 1) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (∃ s : Nat,
          s + r.val.toNat ≤ n ∧
            (RowIncreasing matrix s r.val.toNat ∨ RowDecreasing matrix s r.val.toNat)) ∧
        (∀ (k s : Nat), 1 ≤ k → s + k ≤ n →
          (RowIncreasing matrix s k ∨ RowDecreasing matrix s k) → (k : Int) ≤ r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) (hm : m = 1), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (∃ s : Nat,
          s + r.val.toNat ≤ n ∧
            (RowIncreasing matrix s r.val.toNat ∨ RowDecreasing matrix s r.val.toNat)) ∧
        (∀ (k s : Nat), 1 ≤ k → s + k ≤ n →
          (RowIncreasing matrix s k ∨ RowDecreasing matrix s k) → (k : Int) ≤ r.val)) := by
  sorry

/-- Whenever the function returns a result r and n = 1, r is the maximum k >= 1 for which there exists an integer s with 0 <= s and s + k <= m such that either (for every t with 0 <= t < k-1, matrix[s+t][0] < matrix[s+t+1][0]) or (for every t with 0 <= t < k-1, matrix[s+t][0] > matrix[s+t+1][0]).
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. Also n = 1. -/
theorem spec_9 (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) (hn : n = 1) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (∃ s : Nat,
          s + r.val.toNat ≤ m ∧
            (ColIncreasing matrix s r.val.toNat ∨ ColDecreasing matrix s r.val.toNat)) ∧
        (∀ (k s : Nat), 1 ≤ k → s + k ≤ m →
          (ColIncreasing matrix s k ∨ ColDecreasing matrix s k) → (k : Int) ≤ r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hmn : ValidMatrix matrix m n) (hn : n = 1), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r →
        (∃ s : Nat,
          s + r.val.toNat ≤ m ∧
            (ColIncreasing matrix s r.val.toNat ∨ ColDecreasing matrix s r.val.toNat)) ∧
        (∀ (k s : Nat), 1 ≤ k → s + k ≤ m →
          (ColIncreasing matrix s k ∨ ColDecreasing matrix s k) → (k : Int) ≤ r.val)) := by
  sorry

/-- Whenever longest_increasing_path(A) returns a result r and longest_increasing_path(B) returns a result s, r = s.
  Preconditions: Let A be a valid problem matrix with m = len(A) >= 1 and n = len(A[0]) satisfying 1 <= n <= 200, m <= 200, all rows of A have length n, and 0 <= A[i][j] <= 2147483647 for all cells. Let B be the n x m matrix defined by B[j][i] = A[i][j] for all i,j. -/
theorem spec_10 (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hA : ValidMatrix A m n)
    (hB : mrows B = transposeRows (mrows A) n) :
    ∀ r s : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok r →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok s → r = s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hA : ValidMatrix A m n)
    (hB : mrows B = transposeRows (mrows A) n), ∀ r s : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok r →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok s → r = s) := by
  sorry

/-- Whenever longest_increasing_path(A) returns a result rA and longest_increasing_path(B) returns a result rB, rA = rB.
  Preconditions: Let A and B be valid problem matrices with the same dimensions m x n, where m = len(A) = len(B) >= 1, n = len(A[0]) = len(B[0]) with 1 <= n <= 200, m <= 200, all rows have length n, and all entries of A and B are between 0 and 2147483647. Assume that for every ordered pair of cells (i,j) and (i',j') with 0 <= i,i' < m, 0 <= j,j' < n, and |i-i'| + |j-j'| = 1, the inequality A[i][j] < A[i'][j'] holds if and only if B[i][j] < B[i'][j'] holds. -/
theorem spec_11 (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hA : ValidMatrix A m n) (hB : ValidMatrix B m n)
    (hord : ∀ (i i' j j' : Nat), i < m → i' < m → j < n → j' < n →
      manhattan (i, j) (i', j') = 1 →
        (cell A i j < cell A i' j' ↔ cell B i j < cell B i' j')) :
    ∀ rA rB : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok rA →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok rB → rA = rB := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (m n : Nat)
    (hA : ValidMatrix A m n) (hB : ValidMatrix B m n)
    (hord : ∀ (i i' j j' : Nat), i < m → i' < m → j < n → j' < n →
      manhattan (i, j) (i', j') = 1 →
        (cell A i j < cell A i' j' ↔ cell B i j < cell B i' j')), ∀ rA rB : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok rA →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok rB → rA = rB) := by
  sorry

/-- Whenever longest_increasing_path(A) returns a result rA and longest_increasing_path(B) returns a result rB, rA >= rB.
  Preconditions: Let A be a valid problem matrix with m = len(A) >= 1 and n = len(A[0]) satisfying 1 <= n <= 200, m <= 200, all rows of A have length n, and 0 <= A[i][j] <= 2147483647 for all cells. Let r0,c0,mb,nb be integers with 0 <= r0, 0 <= c0, 1 <= mb, 1 <= nb, r0 + mb <= m, and c0 + nb <= n. Let B be the mb x nb matrix defined by B[i][j] = A[r0+i][c0+j] for 0 <= i < mb and 0 <= j < nb. -/
theorem spec_12 (A B : Slice (alloc.vec.Vec I64)) (m n mb nb r0 c0 : Nat)
    (hA : ValidMatrix A m n)
    (hmb : 1 ≤ mb) (hnb : 1 ≤ nb) (hr0 : r0 + mb ≤ m) (hc0 : c0 + nb ≤ n)
    (hB : mrows B =
      (List.range mb).map fun i => (List.range nb).map fun j => cell A (r0 + i) (c0 + j)) :
    ∀ rA rB : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok rA →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok rB → rB.val ≤ rA.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (A B : Slice (alloc.vec.Vec I64)) (m n mb nb r0 c0 : Nat)
    (hA : ValidMatrix A m n)
    (hmb : 1 ≤ mb) (hnb : 1 ≤ nb) (hr0 : r0 + mb ≤ m) (hc0 : c0 + nb ≤ n)
    (hB : mrows B =
      (List.range mb).map fun i => (List.range nb).map fun j => cell A (r0 + i) (c0 + j)), ∀ rA rB : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path A = ok rA →
        Aegis.LongestIncreasingPath.longest_increasing_path B = ok rB → rB.val ≤ rA.val) := by
  sorry

/-- Let D be the number of distinct integers appearing among the entries matrix[i][j] for 0 <= i < m and 0 <= j < n. Whenever the function returns a result r, r <= D.
  Preconditions: Let m = len(matrix). The input is a valid problem matrix: m >= 1; let n = len(matrix[0]); 1 <= n <= 200; m <= 200; every row matrix[i] has length n; and 0 <= matrix[i][j] <= 2147483647 for every 0 <= i < m and 0 <= j < n. -/
theorem spec_13 (matrix : Slice (alloc.vec.Vec I64)) (m n D : Nat)
    (hmn : ValidMatrix matrix m n)
    (hD : D = ((mrows matrix).flatten).dedup.length) :
    ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r → r.val ≤ (D : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (m n D : Nat)
    (hmn : ValidMatrix matrix m n)
    (hD : D = ((mrows matrix).flatten).dedup.length), ∀ r : I64,
      Aegis.LongestIncreasingPath.longest_increasing_path matrix = ok r → r.val ≤ (D : Int)) := by
  sorry

end AegisSpec.LongestIncreasingPath
