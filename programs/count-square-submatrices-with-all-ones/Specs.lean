import Aegis.CountSquares.Code.Funs

/-!
# Specifications of `Aegis.CountSquares.count_squares`

LeetCode problem `count-square-submatrices-with-all-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CountSquares

  open Aegis.CountSquares

  def height (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    matrix.val.length

  def width (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    (matrix.val.head?.map (fun row => row.val.length)).getD 0

  def get (matrix : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    match matrix.val[i]? with
    | none => 0
    | some row => (row.val[j]?).map (fun x => x.val) |>.getD 0

  def blockOnes (f : ℕ → ℕ → ℤ) (a b k : ℕ) : Prop :=
    ∀ i ∈ Finset.Ico a (a + k), ∀ j ∈ Finset.Ico b (b + k), f i j = 1

  instance instDecidableBlockOnes (f : ℕ → ℕ → ℤ) (a b k : ℕ) :
      Decidable (blockOnes f a b k) := by
    unfold blockOnes
    infer_instance

  def blocksOf (f : ℕ → ℕ → ℤ) (h w : ℕ) : Finset (ℕ × ℕ × ℕ) :=
    ((Finset.range (h + 1)) ×ˢ ((Finset.range (w + 1)) ×ˢ
        (Finset.range (min h w + 1)))).filter
      (fun t => 1 ≤ t.2.2 ∧ t.1 + t.2.2 ≤ h ∧ t.2.1 + t.2.2 ≤ w ∧
        blockOnes f t.1 t.2.1 t.2.2)

  def countSquaresOf (f : ℕ → ℕ → ℤ) (h w : ℕ) : ℕ :=
    (blocksOf f h w).card

  def countSquares (matrix : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
    countSquaresOf (get matrix) (height matrix) (width matrix)

  def numSubSquares (h w : ℕ) : ℕ :=
    ∑ k ∈ Finset.Icc 1 (min h w), (h - k + 1) * (w - k + 1)

  def onesPositions (f : ℕ → ℕ → ℤ) (h w : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range h) ×ˢ (Finset.range w)).filter (fun p => f p.1 p.2 = 1)

  def onesCount (f : ℕ → ℕ → ℤ) (h w : ℕ) : ℕ :=
    (onesPositions f h w).card

  def onesInRow (f : ℕ → ℕ → ℤ) (w i : ℕ) : ℕ :=
    ((Finset.range w).filter (fun j => f i j = 1)).card

  def onesInCol (f : ℕ → ℕ → ℤ) (h j : ℕ) : ℕ :=
    ((Finset.range h).filter (fun i => f i j = 1)).card

  /-- Under the preconditions, the function returns a result r (it does not fail) and r is the number of triples (a,b,k) such that k >= 1, 0 <= a < m, 0 <= b < n, a+k <= m, b+k <= n, and matrix[i][j] = 1 for every i,j with a <= i < a+k and b <= j < b+k. Equivalently, r = sum over k from 1 to min(m,n) of sum over a from 0 to m-k of sum over b from 0 to n-k of c(a,b,k), where c(a,b,k) is 1 exactly when the contiguous k by k block with top-left (a,b) is all ones and is 0 otherwise. Square submatrices have side length at least 1 and are contiguous in both rows and columns.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_1 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∃ r : Std.I64, count_squares matrix = ok r ∧ r.val = (countSquares matrix : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∃ r : Std.I64, count_squares matrix = ok r ∧ r.val = (countSquares matrix : ℤ)) := by
    sorry

  /-- Under the preconditions, the function returns a result r; it does not fail with overflow, out-of-bounds access, or panic.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_2 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∃ r : Std.I64, count_squares matrix = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∃ r : Std.I64, count_squares matrix = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= sum over k from 1 to min(m,n) of (m-k+1)*(n-k+1).
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_3 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        0 ≤ r.val ∧ r.val ≤ (numSubSquares (height matrix) (width matrix) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          0 ≤ r.val ∧ r.val ≤ (numSubSquares (height matrix) (width matrix) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = matrix[0][0].
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. Also m = 1 and n = 1. -/
  theorem spec_4 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hm_one : height matrix = 1) (hn_one : width matrix = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r → r.val = get matrix 0 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hm_one : height matrix = 1) (hn_one : width matrix = 1), ∀ r : Std.I64, count_squares matrix = ok r → r.val = get matrix 0 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. Also matrix[i][j] = 0 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hzero : ∀ i j, i < height matrix → j < width matrix → get matrix i j = 0) :
      ∀ r : Std.I64, count_squares matrix = ok r → r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hzero : ∀ i j, i < height matrix → j < width matrix → get matrix i j = 0), ∀ r : Std.I64, count_squares matrix = ok r → r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = sum over k from 1 to min(m,n) of (m-k+1)*(n-k+1).
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. Also matrix[i][j] = 1 for every i,j with 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hone : ∀ i j, i < height matrix → j < width matrix → get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        r.val = (numSubSquares (height matrix) (width matrix) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hone : ∀ i j, i < height matrix → j < width matrix → get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          r.val = (numSubSquares (height matrix) (width matrix) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of indices j with 0 <= j < n and matrix[0][j] = 1.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. Also m = 1. -/
  theorem spec_7 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hm_one : height matrix = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        r.val = (onesInRow (get matrix) (width matrix) 0 : ℤ) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hm_one : height matrix = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          r.val = (onesInRow (get matrix) (width matrix) 0 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < m and matrix[i][0] = 1.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. Also n = 1. -/
  theorem spec_8 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hn_one : width matrix = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        r.val = (onesInCol (get matrix) (height matrix) 0 : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hn_one : width matrix = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          r.val = (onesInCol (get matrix) (height matrix) 0 : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. There is exactly one pair (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = 1; every other entry is 0. -/
  theorem spec_9 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1)
      (hunique : onesCount (get matrix) (height matrix) (width matrix) = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r → r.val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1)
        (hunique : onesCount (get matrix) (height matrix) (width matrix) = 1), ∀ r : Std.I64, count_squares matrix = ok r → r.val = 1) := by
    sorry

  /-- Whenever the function returns a result r, let ones be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = 1. Then r >= ones.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_10 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        (onesCount (get matrix) (height matrix) (width matrix) : ℤ) ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          (onesCount (get matrix) (height matrix) (width matrix) : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let ones be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = 1. Then r = ones if and only if for every a,b with 0 <= a < m-1 and 0 <= b < n-1, at least one of matrix[a][b], matrix[a][b+1], matrix[a+1][b], matrix[a+1][b+1] is 0.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_11 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        (r.val = (onesCount (get matrix) (height matrix) (width matrix) : ℤ) ↔
          ∀ a b, a < height matrix - 1 → b < width matrix - 1 →
            (get matrix a b = 0 ∨ get matrix a (b + 1) = 0 ∨
              get matrix (a + 1) b = 0 ∨ get matrix (a + 1) (b + 1) = 0)) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          (r.val = (onesCount (get matrix) (height matrix) (width matrix) : ℤ) ↔
            ∀ a b, a < height matrix - 1 → b < width matrix - 1 →
              (get matrix a b = 0 ∨ get matrix a (b + 1) = 0 ∨
                get matrix (a + 1) b = 0 ∨ get matrix (a + 1) (b + 1) = 0))) := by
    sorry

  /-- Whenever the function returns a result r, define MT[i][j] = matrix[j][i] for 0 <= i < n and 0 <= j < m. Then r equals the number of triples (a,b,k) such that k >= 1, 0 <= a < n, 0 <= b < m, a+k <= n, b+k <= m, and MT[i][j] = 1 for every i,j with a <= i < a+k and b <= j < b+k.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_12 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        r.val = (countSquaresOf (fun i j => get matrix j i)
          (width matrix) (height matrix) : ℤ) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          r.val = (countSquaresOf (fun i j => get matrix j i)
            (width matrix) (height matrix) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if matrix[i][j] = 0 for every i,j with 0 <= i < m and 0 <= j < n.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_13 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        (r.val = 0 ↔ ∀ i j, i < height matrix → j < width matrix → get matrix i j = 0) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          (r.val = 0 ↔ ∀ i j, i < height matrix → j < width matrix → get matrix i j = 0)) := by
    sorry

  /-- Whenever the function returns a result r, let ones be the number of pairs (i,j) with 0 <= i < m, 0 <= j < n, and matrix[i][j] = 1. If r > ones, then there exist a,b with 0 <= a < m-1 and 0 <= b < n-1 such that matrix[a][b], matrix[a][b+1], matrix[a+1][b], and matrix[a+1][b+1] are all 1.
    Preconditions: Let m = len(matrix); m is at least 1 and at most 300. Let n = len(matrix[0]); n is at least 1 and at most 300. Every row of matrix has length n, and for every i,j with 0 <= i < m and 0 <= j < n, matrix[i][j] is either 0 or 1. -/
  theorem spec_14 (matrix : Slice (alloc.vec.Vec Std.I64))
      (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
      (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
      (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
      (hentries : ∀ i j, i < height matrix → j < width matrix →
        get matrix i j = 0 ∨ get matrix i j = 1) :
      ∀ r : Std.I64, count_squares matrix = ok r →
        ((onesCount (get matrix) (height matrix) (width matrix) : ℤ) < r.val →
          ∃ a b, a < height matrix - 1 ∧ b < width matrix - 1 ∧
            get matrix a b = 1 ∧ get matrix a (b + 1) = 1 ∧
            get matrix (a + 1) b = 1 ∧ get matrix (a + 1) (b + 1) = 1) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (matrix : Slice (alloc.vec.Vec Std.I64))
        (hm1 : 1 ≤ height matrix) (hm : height matrix ≤ 300)
        (hn1 : 1 ≤ width matrix) (hn : width matrix ≤ 300)
        (hrows : ∀ row ∈ matrix.val, row.val.length = width matrix)
        (hentries : ∀ i j, i < height matrix → j < width matrix →
          get matrix i j = 0 ∨ get matrix i j = 1), ∀ r : Std.I64, count_squares matrix = ok r →
          ((onesCount (get matrix) (height matrix) (width matrix) : ℤ) < r.val →
            ∃ a b, a < height matrix - 1 ∧ b < width matrix - 1 ∧
              get matrix a b = 1 ∧ get matrix a (b + 1) = 1 ∧
              get matrix (a + 1) b = 1 ∧ get matrix (a + 1) (b + 1) = 1)) := by
    sorry

  end AegisSpec.CountSquares
