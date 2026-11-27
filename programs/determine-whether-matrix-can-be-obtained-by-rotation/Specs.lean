import Aegis.FindRotation.Code.Funs

/-!
# Specifications of `Aegis.FindRotation.find_rotation`

LeetCode problem `determine-whether-matrix-can-be-obtained-by-rotation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindRotation

  namespace AegisSpec.FindRotation

  def entry (mat : Slice (alloc.vec.Vec I64)) (i j : ℕ) : ℤ :=
    match mat.val[i]? with
    | some row =>
      match row.val[j]? with
      | some x => x.val
      | none => 0
    | none => 0

  def rowLen (mat : Slice (alloc.vec.Vec I64)) (i : ℕ) : ℕ :=
    match mat.val[i]? with
    | some row => row.val.length
    | none => 0

  def IsBinaryMatrix (mat : Slice (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
    mat.val.length = n ∧
      (∀ i, i < n → rowLen mat i = n) ∧
      (∀ i j, i < n → j < n → entry mat i j = 0 ∨ entry mat i j = 1)

  def rot (n : ℕ) (A : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
    fun i j => A (n - 1 - j) i

  def rotPow (n k : ℕ) (A : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
    Nat.iterate (rot n) k A

  def transpose (A : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
    fun i j => A j i

  def IsRotation (mat target : Slice (alloc.vec.Vec I64)) (n k : ℕ) : Prop :=
    ∀ i j, i < n → j < n → entry target i j = rotPow n k (entry mat) i j

  def IsTranspose (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ) : Prop :=
    ∀ i j, i < n → j < n → entry target i j = entry mat j i

  /-- Define the clockwise 90-degree rotation R(A) of an n x n matrix A by R(A)[i][j] = A[n-1-j][i] for 0 <= i,j < n, and set R^0(A)=A, R^1(A)=R(A), R^2(A)=R(R(A)), R^3(A)=R(R(R(A))). Whenever find_rotation(mat, target) returns a Bool r, r = true if and only if there exists k in {0,1,2,3} such that target[i][j] = R^k(mat)[i][j] for every 0 <= i,j < n.
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_1 (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
      (r : Bool) (hr : find_rotation mat target = ok r) :
      (r = true ↔ ∃ k, k < 4 ∧ IsRotation mat target n k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
        (r : Bool) (hr : find_rotation mat target = ok r), (r = true ↔ ∃ k, k < 4 ∧ IsRotation mat target n k)) := by
    sorry

  /-- For every input satisfying the preconditions, find_rotation(mat, target) returns a result r (a Bool); it does not fail, panic, overflow, or access any index outside 0 <= i,j < n.
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_2 (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n) :
      ∃ r : Bool, find_rotation mat target = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n), ∃ r : Bool, find_rotation mat target = ok r) := by
    sorry

  /-- Define R(A)[i][j] = A[n-1-j][i] for 0 <= i,j < n. Let mat' be the n x n matrix with mat'[i][j] = R(mat)[i][j] for every 0 <= i,j < n. Whenever find_rotation(mat, target) returns r1 and find_rotation(mat', target) returns r2, r1 = r2.
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_3 (mat target mat' : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
      (hmat'_dim : mat'.val.length = n)
      (hmat'_rows : ∀ i, i < n → rowLen mat' i = n)
      (hmat'_rot : ∀ i j, i < n → j < n → entry mat' i j = entry mat (n - 1 - j) i)
      (r1 r2 : Bool)
      (h1 : find_rotation mat target = ok r1)
      (h2 : find_rotation mat' target = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat target mat' : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
        (hmat'_dim : mat'.val.length = n)
        (hmat'_rows : ∀ i, i < n → rowLen mat' i = n)
        (hmat'_rot : ∀ i j, i < n → j < n → entry mat' i j = entry mat (n - 1 - j) i)
        (r1 r2 : Bool)
        (h1 : find_rotation mat target = ok r1)
        (h2 : find_rotation mat' target = ok r2), r1 = r2) := by
    sorry

  /-- Define R(A)[i][j] = A[n-1-j][i] for 0 <= i,j < n. Let target' be the n x n matrix with target'[i][j] = R(target)[i][j] for every 0 <= i,j < n. Whenever find_rotation(mat, target) returns r1 and find_rotation(mat, target') returns r2, r1 = r2.
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_4 (mat target target' : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
      (htarget'_dim : target'.val.length = n)
      (htarget'_rows : ∀ i, i < n → rowLen target' i = n)
      (htarget'_rot : ∀ i j, i < n → j < n → entry target' i j = entry target (n - 1 - j) i)
      (r1 r2 : Bool)
      (h1 : find_rotation mat target = ok r1)
      (h2 : find_rotation mat target' = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat target target' : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
        (htarget'_dim : target'.val.length = n)
        (htarget'_rows : ∀ i, i < n → rowLen target' i = n)
        (htarget'_rot : ∀ i j, i < n → j < n → entry target' i j = entry target (n - 1 - j) i)
        (r1 r2 : Bool)
        (h1 : find_rotation mat target = ok r1)
        (h2 : find_rotation mat target' = ok r2), r1 = r2) := by
    sorry

  /-- Define transpose T(A) by T(A)[i][j] = A[j][i] for 0 <= i,j < n. Whenever find_rotation(mat, target) returns r1 and find_rotation(T(mat), T(target)) returns r2, r1 = r2.
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_5 (mat target matT targetT : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
      (hmatT_dim : matT.val.length = n)
      (hmatT_rows : ∀ i, i < n → rowLen matT i = n)
      (htargetT_dim : targetT.val.length = n)
      (htargetT_rows : ∀ i, i < n → rowLen targetT i = n)
      (hmatT : IsTranspose mat matT n)
      (htargetT : IsTranspose target targetT n)
      (r1 r2 : Bool)
      (h1 : find_rotation mat target = ok r1)
      (h2 : find_rotation matT targetT = ok r2) :
      r1 = r2 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat target matT targetT : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
        (hmatT_dim : matT.val.length = n)
        (hmatT_rows : ∀ i, i < n → rowLen matT i = n)
        (htargetT_dim : targetT.val.length = n)
        (htargetT_rows : ∀ i, i < n → rowLen targetT i = n)
        (hmatT : IsTranspose mat matT n)
        (htargetT : IsTranspose target targetT n)
        (r1 r2 : Bool)
        (h1 : find_rotation mat target = ok r1)
        (h2 : find_rotation matT targetT = ok r2), r1 = r2) := by
    sorry

  /-- Whenever find_rotation(mat, target) returns a Bool r with r = true, the number of entries equal to 1 in mat equals the number of entries equal to 1 in target; that is, sum over 0 <= i,j < n of mat[i][j] equals sum over 0 <= i,j < n of target[i][j].
    Preconditions: Let n = len(mat). Assume 1 <= n <= 10, len(target) = n, len(mat[i]) = n for every 0 <= i < n, len(target[i]) = n for every 0 <= i < n, and mat[i][j] and target[i][j] are each either 0 or 1 for every 0 <= i < n and 0 <= j < n. -/
  theorem spec_6 (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
      (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
      (r : Bool) (hr : find_rotation mat target = ok r) (hrt : r = true) :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, entry mat i j)
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, entry target i j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat target : Slice (alloc.vec.Vec I64)) (n : ℕ)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10)
        (hmat : IsBinaryMatrix mat n) (htarget : IsBinaryMatrix target n)
        (r : Bool) (hr : find_rotation mat target = ok r) (hrt : r = true), (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, entry mat i j)
          = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, entry target i j) := by
    sorry

  end AegisSpec.FindRotation
