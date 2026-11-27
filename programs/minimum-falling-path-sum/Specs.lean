import Aegis.MinFallingPathSum.Code.Funs

/-!
# Specifications of `Aegis.MinFallingPathSum.min_falling_path_sum`

LeetCode problem `minimum-falling-path-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinFallingPathSum

  namespace AegisSpec.MinFallingPathSum

  def entry (matrix : Slice (alloc.vec.Vec I64)) (i j : Nat) : Int :=
    match matrix.val[i]? with
    | none => 0
    | some row =>
      match row.val[j]? with
      | none => 0
      | some x => x.val

  def HasShape (matrix : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    matrix.val.length = n ∧
      ∀ i, i < n → ∃ row, matrix.val[i]? = some row ∧ row.val.length = n

  def EntriesInRange (matrix : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    ∀ i j, i < n → j < n → -100 ≤ entry matrix i j ∧ entry matrix i j ≤ 100

  def IsValidInput (matrix : Slice (alloc.vec.Vec I64)) (n : Nat) : Prop :=
    1 ≤ n ∧ n ≤ 100 ∧ HasShape matrix n ∧ EntriesInRange matrix n

  def pathSum (matrix : Slice (alloc.vec.Vec I64)) (n : Nat) (c : Nat → Nat) : Int :=
    (Finset.range n).sum fun i => entry matrix i (c i)

  def IsFallingPath (n : Nat) (c : Nat → Nat) : Prop :=
    (∀ i, i < n → c i < n) ∧
      ∀ i, i + 1 < n → |((c (i + 1) : Int) - (c i))| ≤ 1

  def fallingPathSums (matrix : Slice (alloc.vec.Vec I64)) (n : Nat) : Set Int :=
    {s | ∃ c : Nat → Nat, IsFallingPath n c ∧ s = pathSum matrix n c}

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def rowMin (matrix : Slice (alloc.vec.Vec I64)) (n i : Nat) : Int :=
    listMin ((List.range n).map fun j => entry matrix i j)

  def rowMax (matrix : Slice (alloc.vec.Vec I64)) (n i : Nat) : Int :=
    listMax ((List.range n).map fun j => entry matrix i j)

  /-- The function returns a result r, and r is the least possible sum of a falling path: r = min { sum_{i=0}^{n-1} matrix[i][c_i] : c_0,...,c_{n-1} are column indices with 0 <= c_i < n for all i and |c_{i+1} - c_i| <= 1 for all 0 <= i < n-1 }. Equivalently, every falling path has sum at least r, and some falling path has sum exactly r.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_1
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∃ r : I64, min_falling_path_sum matrix = ok r ∧
        IsLeast (fallingPathSums matrix n) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∃ r : I64, min_falling_path_sum matrix = ok r ∧
          IsLeast (fallingPathSums matrix n) r.val) := by
    sorry

  /-- For every matrix satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_2
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∃ r : I64, min_falling_path_sum matrix = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∃ r : I64, min_falling_path_sum matrix = ok r) := by
    sorry

  /-- Whenever the function returns a result r, with n = len(matrix), we have r >= -100 * n.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_3
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∀ r : I64, min_falling_path_sum matrix = ok r → r.val ≥ -100 * (n : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∀ r : I64, min_falling_path_sum matrix = ok r → r.val ≥ -100 * (n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, with n = len(matrix), we have r <= 100 * n.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_4
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∀ r : I64, min_falling_path_sum matrix = ok r → r.val ≤ 100 * (n : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∀ r : I64, min_falling_path_sum matrix = ok r → r.val ≤ 100 * (n : Int)) := by
    sorry

  /-- Whenever the function returns a result r, for every falling path c_0,...,c_{n-1} (where 0 <= c_i < n for all i and |c_{i+1}-c_i| <= 1 for all 0 <= i < n-1), we have r <= sum_{i=0}^{n-1} matrix[i][c_i].
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_5
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∀ r : I64, min_falling_path_sum matrix = ok r →
        ∀ c : Nat → Nat, IsFallingPath n c → r.val ≤ pathSum matrix n c := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∀ r : I64, min_falling_path_sum matrix = ok r →
          ∀ c : Nat → Nat, IsFallingPath n c → r.val ≤ pathSum matrix n c) := by
    sorry

  /-- Whenever the function returns a result r, there exists a falling path c_0,...,c_{n-1} (where 0 <= c_i < n for all i and |c_{i+1}-c_i| <= 1 for all 0 <= i < n-1) such that r = sum_{i=0}^{n-1} matrix[i][c_i].
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_6
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∀ r : I64, min_falling_path_sum matrix = ok r →
        ∃ c : Nat → Nat, IsFallingPath n c ∧ r.val = pathSum matrix n c := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∀ r : I64, min_falling_path_sum matrix = ok r →
          ∃ c : Nat → Nat, IsFallingPath n c ∧ r.val = pathSum matrix n c) := by
    sorry

  /-- Whenever the function returns a result r, let row_min(i) = min { matrix[i][j] : 0 <= j < n } and row_max(i) = max { matrix[i][j] : 0 <= j < n } for each 0 <= i < n; then sum_{i=0}^{n-1} row_min(i) <= r <= sum_{i=0}^{n-1} row_max(i).
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; and for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100. -/
  theorem spec_7
      (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n) :
      ∀ r : I64, min_falling_path_sum matrix = ok r →
        (Finset.range n).sum (fun i => rowMin matrix n i) ≤ r.val ∧
          r.val ≤ (Finset.range n).sum (fun i => rowMax matrix n i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n), ∀ r : I64, min_falling_path_sum matrix = ok r →
          (Finset.range n).sum (fun i => rowMin matrix n i) ≤ r.val ∧
            r.val ≤ (Finset.range n).sum (fun i => rowMax matrix n i)) := by
    sorry

  /-- Let matrix' be defined by matrix'[i][j] = matrix[i][j] + c for all i,j. If the function returns r on matrix and returns r' on matrix', then r' = r + n * c.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100; and c is an integer such that -100 <= matrix[i][j] + c <= 100 for all i,j. -/
  theorem spec_8
      (matrix matrix' : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n)
      (h' : HasShape matrix' n)
      (c : Int)
      (hc : ∀ i j, i < n → j < n →
        -100 ≤ entry matrix i j + c ∧ entry matrix i j + c ≤ 100)
      (hdef : ∀ i j, i < n → j < n → entry matrix' i j = entry matrix i j + c) :
      ∀ r r' : I64, min_falling_path_sum matrix = ok r →
        min_falling_path_sum matrix' = ok r' → r'.val = r.val + (n : Int) * c := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix matrix' : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n)
        (h' : HasShape matrix' n)
        (c : Int)
        (hc : ∀ i j, i < n → j < n →
          -100 ≤ entry matrix i j + c ∧ entry matrix i j + c ≤ 100)
        (hdef : ∀ i j, i < n → j < n → entry matrix' i j = entry matrix i j + c), ∀ r r' : I64, min_falling_path_sum matrix = ok r →
          min_falling_path_sum matrix' = ok r' → r'.val = r.val + (n : Int) * c) := by
    sorry

  /-- Let matrix' be defined by matrix'[i][j] = c * matrix[i][j] for all i,j. If the function returns r on matrix and returns r' on matrix', then r' = c * r.
    Preconditions: Let n = len(matrix). The matrix is a non-empty square slice: 1 <= n <= 100; for every i with 0 <= i < n, len(matrix[i]) = n; for every i,j with 0 <= i < n and 0 <= j < n, -100 <= matrix[i][j] <= 100; and c is a nonnegative integer such that -100 <= c * matrix[i][j] <= 100 for all i,j. -/
  theorem spec_9
      (matrix matrix' : Slice (alloc.vec.Vec I64)) (n : Nat)
      (h : IsValidInput matrix n)
      (h' : HasShape matrix' n)
      (c : Nat)
      (hc : ∀ i j, i < n → j < n →
        -100 ≤ (c : Int) * entry matrix i j ∧ (c : Int) * entry matrix i j ≤ 100)
      (hdef : ∀ i j, i < n → j < n → entry matrix' i j = (c : Int) * entry matrix i j) :
      ∀ r r' : I64, min_falling_path_sum matrix = ok r →
        min_falling_path_sum matrix' = ok r' → r'.val = (c : Int) * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix matrix' : Slice (alloc.vec.Vec I64)) (n : Nat)
        (h : IsValidInput matrix n)
        (h' : HasShape matrix' n)
        (c : Nat)
        (hc : ∀ i j, i < n → j < n →
          -100 ≤ (c : Int) * entry matrix i j ∧ (c : Int) * entry matrix i j ≤ 100)
        (hdef : ∀ i j, i < n → j < n → entry matrix' i j = (c : Int) * entry matrix i j), ∀ r r' : I64, min_falling_path_sum matrix = ok r →
          min_falling_path_sum matrix' = ok r' → r'.val = (c : Int) * r.val) := by
    sorry

  end AegisSpec.MinFallingPathSum
