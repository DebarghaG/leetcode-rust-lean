import Aegis.MaxSideLength.Code.Funs

/-!
# Specifications of `Aegis.MaxSideLength.max_side_length`

LeetCode problem `maximum-side-length-of-a-square-with-sum-less-than-or-equal-to-threshold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSideLength

def nrows (mat : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  mat.val.length

def row (mat : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : List ℤ :=
  match (mat.val)[i]? with
  | some v => v.val.map (fun x => x.val)
  | none => []

def ncols (mat : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  (row mat 0).length

def entry (mat : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
  (row mat i).getD j 0

def minSide (mat : Slice (alloc.vec.Vec Std.I64)) : ℕ :=
  min (nrows mat) (ncols mat)

def sqSum (mat : Slice (alloc.vec.Vec Std.I64)) (a b k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k, entry mat (a + i) (b + j)

def totalSum (mat : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
  ∑ i ∈ Finset.range (nrows mat), ∑ j ∈ Finset.range (ncols mat), entry mat i j

def Fits (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : ℤ) (k : ℕ) : Prop :=
  ∃ a b : ℕ, a + k ≤ nrows mat ∧ b + k ≤ ncols mat ∧ sqSum mat a b k ≤ threshold

def NoFits (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : ℤ) (k : ℕ) : Prop :=
  ∀ a b : ℕ, a + k ≤ nrows mat → b + k ≤ ncols mat → threshold < sqSum mat a b k

def ZeroSquare (mat : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : Prop :=
  k = 0 ∨
    ∃ a b : ℕ, a + k ≤ nrows mat ∧ b + k ≤ ncols mat ∧
      ∀ i j : ℕ, i < k → j < k → entry mat (a + i) (b + j) = 0

def ValidMat (mat : Slice (alloc.vec.Vec Std.I64)) : Prop :=
  1 ≤ nrows mat ∧ nrows mat ≤ 300 ∧
  1 ≤ ncols mat ∧ ncols mat ≤ 300 ∧
  (∀ i : ℕ, i < nrows mat → (row mat i).length = ncols mat) ∧
  (∀ i j : ℕ, i < nrows mat → j < ncols mat →
    0 ≤ entry mat i j ∧ entry mat i j ≤ 10000)

def ValidInput (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64) : Prop :=
  ValidMat mat ∧ 0 ≤ threshold.val ∧ threshold.val ≤ 100000

/-- The function returns a result r, and r is the maximum side length of a contiguous square submatrix whose sum is at most threshold, in the following exact sense: 0 <= r <= min(m,n); if r >= 1 then there exist a and b with 0 <= a <= m-r and 0 <= b <= n-r such that S(a,b,r) <= threshold; and for every s with r < s <= min(m,n) and every a and b with 0 <= a <= m-s and 0 <= b <= n-s, S(a,b,s) > threshold.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. For 0 <= a, 0 <= b, and k >= 1 with a+k <= m and b+k <= n, write S(a,b,k) = sum_{i=0}^{k-1} sum_{j=0}^{k-1} mat[a+i][b+j]. -/
theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) :
    ∃ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ (minSide mat : ℤ) ∧
        (1 ≤ r.val → Fits mat threshold.val r.val.toNat) ∧
        (∀ s : ℕ, r.val < (s : ℤ) → s ≤ minSide mat → NoFits mat threshold.val s) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold), ∃ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r ∧
        0 ≤ r.val ∧
        r.val ≤ (minSide mat : ℤ) ∧
        (1 ≤ r.val → Fits mat threshold.val r.val.toNat) ∧
        (∀ s : ℕ, r.val < (s : ℤ) → s ≤ minSide mat → NoFits mat threshold.val s)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. -/
theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) :
    ∃ r : Std.I64, Aegis.MaxSideLength.max_side_length mat threshold = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold), ∃ r : Std.I64, Aegis.MaxSideLength.max_side_length mat threshold = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every s with 1 <= s <= min(m,n) and every a and b with 0 <= a <= m-s and 0 <= b <= n-s, S(a,b,s) > threshold.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. For 0 <= a, 0 <= b, and k >= 1 with a+k <= m and b+k <= n, write S(a,b,k) = sum_{i=0}^{k-1} sum_{j=0}^{k-1} mat[a+i][b+j]. -/
theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) :
    ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        (r.val = 0 ↔
          ∀ s : ℕ, 1 ≤ s → s ≤ minSide mat → NoFits mat threshold.val s) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold), ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        (r.val = 0 ↔
          ∀ s : ℕ, 1 ≤ s → s ≤ minSide mat → NoFits mat threshold.val s)) := by
  sorry

/-- Whenever the function returns a result r, for every k with 1 <= k <= r there exist a and b with 0 <= a <= m-k and 0 <= b <= n-k such that S(a,b,k) <= threshold.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. For 0 <= a, 0 <= b, and k >= 1 with a+k <= m and b+k <= n, write S(a,b,k) = sum_{i=0}^{k-1} sum_{j=0}^{k-1} mat[a+i][b+j]. -/
theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) :
    ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        ∀ k : ℕ, 1 ≤ k → (k : ℤ) ≤ r.val → Fits mat threshold.val k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold), ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        ∀ k : ℕ, 1 ≤ k → (k : ℤ) ≤ r.val → Fits mat threshold.val k) := by
  sorry

/-- If max_side_length(mat,t1) returns r1 and max_side_length(mat,t2) returns r2, then r1 <= r2.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= t1 <= t2 <= 100000. -/
theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (t1 t2 : Std.I64)
    (hm : ValidMat mat) (h1 : 0 ≤ t1.val) (h12 : t1.val ≤ t2.val)
    (h2 : t2.val ≤ 100000) :
    ∀ r1 r2 : Std.I64,
      Aegis.MaxSideLength.max_side_length mat t1 = ok r1 →
        Aegis.MaxSideLength.max_side_length mat t2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (t1 t2 : Std.I64)
    (hm : ValidMat mat) (h1 : 0 ≤ t1.val) (h12 : t1.val ≤ t2.val)
    (h2 : t2.val ≤ 100000), ∀ r1 r2 : Std.I64,
      Aegis.MaxSideLength.max_side_length mat t1 = ok r1 →
        Aegis.MaxSideLength.max_side_length mat t2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If max_side_length(matA,threshold) returns rA and max_side_length(matB,threshold) returns rB, then rA >= rB.
  Preconditions: Let matA and matB be matrices satisfying the problem constraints with the same dimensions m and n: 1 <= m <= 300, 1 <= n <= 300, len(matA[i]) = len(matB[i]) = n for every 0 <= i < m, all entries of both matrices lie in 0..10000, and 0 <= threshold <= 100000. Suppose matA[i][j] <= matB[i][j] for every 0 <= i < m and 0 <= j < n. -/
theorem spec_6 (matA matB : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (hA : ValidMat matA) (hB : ValidMat matB)
    (hdim : nrows matA = nrows matB ∧ ncols matA = ncols matB)
    (hentries : ∀ i j : ℕ, i < nrows matA → j < ncols matA →
      entry matA i j ≤ entry matB i j)
    (hth : 0 ≤ threshold.val ∧ threshold.val ≤ 100000) :
    ∀ rA rB : Std.I64,
      Aegis.MaxSideLength.max_side_length matA threshold = ok rA →
        Aegis.MaxSideLength.max_side_length matB threshold = ok rB →
          rB.val ≤ rA.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (matA matB : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (hA : ValidMat matA) (hB : ValidMat matB)
    (hdim : nrows matA = nrows matB ∧ ncols matA = ncols matB)
    (hentries : ∀ i j : ℕ, i < nrows matA → j < ncols matA →
      entry matA i j ≤ entry matB i j)
    (hth : 0 ≤ threshold.val ∧ threshold.val ≤ 100000), ∀ rA rB : Std.I64,
      Aegis.MaxSideLength.max_side_length matA threshold = ok rA →
        Aegis.MaxSideLength.max_side_length matB threshold = ok rB →
          rB.val ≤ rA.val) := by
  sorry

/-- Whenever the function returns a result r, if threshold >= sum_{i=0}^{m-1} sum_{j=0}^{n-1} mat[i][j], then r = min(m,n).
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. -/
theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) :
    ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        totalSum mat ≤ threshold.val → r.val = (minSide mat : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold), ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        totalSum mat ≤ threshold.val → r.val = (minSide mat : ℤ)) := by
  sorry

/-- Whenever the function returns a result r with threshold = 0, r is the largest k with 0 <= k <= min(m,n) such that either k = 0 or there exist a and b with 0 <= a <= m-k and 0 <= b <= n-k and mat[a+i][b+j] = 0 for every 0 <= i < k and 0 <= j < k.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and threshold = 0. -/
theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) (hth : threshold.val = 0) :
    ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        0 ≤ r.val ∧
          r.val ≤ (minSide mat : ℤ) ∧
          ZeroSquare mat r.val.toNat ∧
          (∀ k : ℕ, k ≤ minSide mat → ZeroSquare mat k → (k : ℤ) ≤ r.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold) (hth : threshold.val = 0), ∀ r : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        0 ≤ r.val ∧
          r.val ≤ (minSide mat : ℤ) ∧
          ZeroSquare mat r.val.toNat ∧
          (∀ k : ℕ, k ≤ minSide mat → ZeroSquare mat k → (k : ℤ) ≤ r.val)) := by
  sorry

/-- If max_side_length(mat,threshold) returns r and max_side_length(T,threshold) returns rT, then r = rT.
  Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies 1 <= m <= 300, 1 <= n <= 300, len(mat[i]) = n for every 0 <= i < m, 0 <= mat[i][j] <= 10000 for every 0 <= i < m and 0 <= j < n, and 0 <= threshold <= 100000. Let T be the n by m matrix with T[i][j] = mat[j][i] for every 0 <= i < n and 0 <= j < m. -/
theorem spec_9 (mat T : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold)
    (hT : nrows T = ncols mat ∧ ncols T = nrows mat ∧
      ∀ i j : ℕ, i < nrows T → j < ncols T → entry T i j = entry mat j i) :
    ∀ r rT : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        Aegis.MaxSideLength.max_side_length T threshold = ok rT → r.val = rT.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat T : Slice (alloc.vec.Vec Std.I64)) (threshold : Std.I64)
    (h : ValidInput mat threshold)
    (hT : nrows T = ncols mat ∧ ncols T = nrows mat ∧
      ∀ i j : ℕ, i < nrows T → j < ncols T → entry T i j = entry mat j i), ∀ r rT : Std.I64,
      Aegis.MaxSideLength.max_side_length mat threshold = ok r →
        Aegis.MaxSideLength.max_side_length T threshold = ok rT → r.val = rT.val) := by
  sorry

end AegisSpec.MaxSideLength
