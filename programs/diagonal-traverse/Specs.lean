import Aegis.FindDiagonalOrder.Code.Funs

/-!
# Specifications of `Aegis.FindDiagonalOrder.find_diagonal_order`

LeetCode problem `diagonal-traverse`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.FindDiagonalOrder

  namespace AegisSpec.FindDiagonalOrder

  def numRows (mat : Slice (alloc.vec.Vec Std.I64)) : Nat := mat.val.length

  def numCols (mat : Slice (alloc.vec.Vec Std.I64)) : Nat :=
    ((mat.val[0]?).map (fun row => row.val.length)).getD 0

  def rowLen? (mat : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option Nat :=
    (mat.val[i]?).map (fun row => row.val.length)

  def entry (mat : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
    (((mat.val[i]?).bind (fun row => row.val[j]?)).map (fun x => x.val)).getD 0

  def flat (mat : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    (List.range (numRows mat)).flatMap
      (fun i => (List.range (numCols mat)).map (fun j => entry mat i j))

  def outList (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

  def outGet? (r : alloc.vec.Vec Std.I64) (p : Nat) : Option ℤ := (outList r)[p]?

  def win (r : alloc.vec.Vec Std.I64) (start L : Nat) : List ℤ :=
    ((outList r).drop start).take L

  def countEq (l : List ℤ) (v : ℤ) : Nat := (l.filter (fun x => x = v)).length

  def diagLo (mat : Slice (alloc.vec.Vec Std.I64)) (s : Nat) : Nat := s - (numCols mat - 1)

  def diagHi (mat : Slice (alloc.vec.Vec Std.I64)) (s : Nat) : Nat :=
    min s (numRows mat - 1)

  def diagLen (mat : Slice (alloc.vec.Vec Std.I64)) (s : Nat) : Nat :=
    diagHi mat s - diagLo mat s + 1

  def diagStart (mat : Slice (alloc.vec.Vec Std.I64)) (s : Nat) : Nat :=
    ((List.range s).map (fun t => diagLen mat t)).sum

  def diagEntry (mat : Slice (alloc.vec.Vec Std.I64)) (s k : Nat) : ℤ :=
    entry mat (diagLo mat s + k) (s - (diagLo mat s + k))

  def diagList (mat : Slice (alloc.vec.Vec Std.I64)) (s : Nat) : List ℤ :=
    (List.range (diagLen mat s)).map (fun k => diagEntry mat s k)

  def Valid (mat : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    1 ≤ numRows mat ∧
    1 ≤ numCols mat ∧
    numRows mat * numCols mat ≤ 10000 ∧
    (∀ i : Nat, i < numRows mat → rowLen? mat i = some (numCols mat)) ∧
    (∀ i j : Nat, i < numRows mat → j < numCols mat →
      -100000 ≤ entry mat i j ∧ entry mat i j ≤ 100000)

  /-- Let a_s = max(0, s-(n-1)), b_s = min(s, m-1), L_s = b_s-a_s+1 for 0 <= s <= m+n-2, and let D_s be the list of length L_s with D_s[k] = mat[a_s+k][s-(a_s+k)] for 0 <= k < L_s. Let start_s = sum_{t=0}^{s-1} L_t. The function returns a result r such that len(r) = m*n and, for every s with 0 <= s <= m+n-2 and every k with 0 <= k < L_s, r[start_s+k] = D_s[k] when s is odd, and r[start_s+k] = D_s[L_s-1-k] when s is even.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        (∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 1 →
          ∀ k : Nat, k < diagLen mat s →
            outGet? r (diagStart mat s + k) = some (diagEntry mat s k)) ∧
        (∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 0 →
          ∀ k : Nat, k < diagLen mat s →
            outGet? r (diagStart mat s + k) =
              some (diagEntry mat s (diagLen mat s - 1 - k))) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          (∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 1 →
            ∀ k : Nat, k < diagLen mat s →
              outGet? r (diagStart mat s + k) = some (diagEntry mat s k)) ∧
          (∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 0 →
            ∀ k : Nat, k < diagLen mat s →
              outGet? r (diagStart mat s + k) =
                some (diagEntry mat s (diagLen mat s - 1 - k)))) := by
    sorry

  /-- The function returns a result r and len(r) = m*n.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; in particular it does not fail.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64, find_diagonal_order mat = ok r := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64, find_diagonal_order mat = ok r) := by
    sorry

  /-- The function returns a result r such that, for every integer v, the number of indices p with 0 <= p < len(r) and r[p] = v equals the number of pairs (i,j) with 0 <= i < m, 0 <= j < n and mat[i][j] = v.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        ∀ v : ℤ, countEq (outList r) v = countEq (flat mat) v := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          ∀ v : ℤ, countEq (outList r) v = countEq (flat mat) v) := by
    sorry

  /-- The function returns a result r such that, for every p with 0 <= p < len(r), there exist i and j with 0 <= i < m, 0 <= j < n, and r[p] = mat[i][j].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        ∀ p : Nat, p < r.val.length →
          ∃ i j : Nat,
            i < numRows mat ∧ j < numCols mat ∧ outGet? r p = some (entry mat i j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          ∀ p : Nat, p < r.val.length →
            ∃ i j : Nat,
              i < numRows mat ∧ j < numCols mat ∧ outGet? r p = some (entry mat i j)) := by
    sorry

  /-- The function returns a result r such that, for every p with 0 <= p < len(r), -100000 <= r[p] <= 100000.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        ∀ p : Nat, p < r.val.length → ∀ v : ℤ, outGet? r p = some v →
          -100000 ≤ v ∧ v ≤ 100000 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          ∀ p : Nat, p < r.val.length → ∀ v : ℤ, outGet? r p = some v →
            -100000 ≤ v ∧ v ≤ 100000) := by
    sorry

  /-- The function returns a result r such that len(r) >= 1 and r[0] = mat[0][0].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        1 ≤ r.val.length ∧ outGet? r 0 = some (entry mat 0 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          1 ≤ r.val.length ∧ outGet? r 0 = some (entry mat 0 0)) := by
    sorry

  /-- The function returns a result r such that len(r) = m*n and r[m*n-1] = mat[m-1][n-1].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        outGet? r (numRows mat * numCols mat - 1) =
          some (entry mat (numRows mat - 1) (numCols mat - 1)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          outGet? r (numRows mat * numCols mat - 1) =
            some (entry mat (numRows mat - 1) (numCols mat - 1))) := by
    sorry

  /-- If m = 1, then the function returns a result r such that len(r) = n and, for every j with 0 <= j < n, r[j] = mat[0][j].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat)
      (hm : numRows mat = 1) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numCols mat ∧
        ∀ j : Nat, j < numCols mat → outGet? r j = some (entry mat 0 j) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat)
        (hm : numRows mat = 1), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numCols mat ∧
          ∀ j : Nat, j < numCols mat → outGet? r j = some (entry mat 0 j)) := by
    sorry

  /-- If n = 1, then the function returns a result r such that len(r) = m and, for every i with 0 <= i < m, r[i] = mat[i][0].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_10 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat)
      (hn : numCols mat = 1) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat ∧
        ∀ i : Nat, i < numRows mat → outGet? r i = some (entry mat i 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat)
        (hn : numCols mat = 1), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat ∧
          ∀ i : Nat, i < numRows mat → outGet? r i = some (entry mat i 0)) := by
    sorry

  /-- Let a_s = max(0, s-(n-1)), b_s = min(s, m-1), L_s = b_s-a_s+1 for 0 <= s <= m+n-2, D_s[k] = mat[a_s+k][s-(a_s+k)] for 0 <= k < L_s, and start_s = sum_{t=0}^{s-1} L_t (with start_0 = 0). The function returns a result r such that len(r) = m*n and, for every s with 0 <= s <= m+n-2 and every integer v, the number of k with 0 <= k < L_s and r[start_s+k] = v equals the number of k with 0 <= k < L_s and D_s[k] = v.
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_11 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 →
          ∀ v : ℤ,
            countEq (win r (diagStart mat s) (diagLen mat s)) v =
              countEq (diagList mat s) v := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 →
            ∀ v : ℤ,
              countEq (win r (diagStart mat s) (diagLen mat s)) v =
                countEq (diagList mat s) v) := by
    sorry

  /-- Let a_s = max(0, s-(n-1)), b_s = min(s, m-1), L_s = b_s-a_s+1 for 0 <= s <= m+n-2, D_s[k] = mat[a_s+k][s-(a_s+k)] for 0 <= k < L_s, and start_s = sum_{t=0}^{s-1} L_t (with start_0 = 0). The function returns a result r such that len(r) = m*n and, for every even s with 0 <= s <= m+n-2 and every k with 0 <= k < L_s, r[start_s+k] = D_s[L_s-1-k].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 0 →
          ∀ k : Nat, k < diagLen mat s →
            outGet? r (diagStart mat s + k) =
              some (diagEntry mat s (diagLen mat s - 1 - k)) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 0 →
            ∀ k : Nat, k < diagLen mat s →
              outGet? r (diagStart mat s + k) =
                some (diagEntry mat s (diagLen mat s - 1 - k))) := by
    sorry

  /-- Let a_s = max(0, s-(n-1)), b_s = min(s, m-1), L_s = b_s-a_s+1 for 0 <= s <= m+n-2, D_s[k] = mat[a_s+k][s-(a_s+k)] for 0 <= k < L_s, and start_s = sum_{t=0}^{s-1} L_t (with start_0 = 0). The function returns a result r such that len(r) = m*n and, for every odd s with 0 <= s <= m+n-2 and every k with 0 <= k < L_s, r[start_s+k] = D_s[k].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_13 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 1 →
          ∀ k : Nat, k < diagLen mat s →
            outGet? r (diagStart mat s + k) = some (diagEntry mat s k) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 → s % 2 = 1 →
            ∀ k : Nat, k < diagLen mat s →
              outGet? r (diagStart mat s + k) = some (diagEntry mat s k)) := by
    sorry

  /-- Let a_s = max(0, s-(n-1)), b_s = min(s, m-1), L_s = b_s-a_s+1 for 0 <= s <= m+n-2, and start_s = sum_{t=0}^{s-1} L_t (with start_0 = 0). For each p with 0 <= p < m*n, let s(p) be the unique s with start_s <= p < start_s + L_s. The function returns a result r such that len(r) = m*n and, for every p with 0 <= p < m*n, there exist i and j with 0 <= i < m, 0 <= j < n, i+j = s(p), and r[p] = mat[i][j].
    Preconditions: Let m = len(mat) and n = len(mat[0]). The input satisfies m >= 1, n >= 1, m*n <= 10000, every row mat[i] has length exactly n for 0 <= i < m, and -100000 <= mat[i][j] <= 100000 for all 0 <= i < m and 0 <= j < n. All indices are 0-based. -/
  theorem spec_14 (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat) :
      ∃ r : alloc.vec.Vec Std.I64,
        find_diagonal_order mat = ok r ∧
        r.val.length = numRows mat * numCols mat ∧
        ∀ p : Nat, p < numRows mat * numCols mat →
          ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 →
            diagStart mat s ≤ p → p < diagStart mat s + diagLen mat s →
              ∃ i j : Nat,
                i < numRows mat ∧ j < numCols mat ∧ i + j = s ∧
                  outGet? r p = some (entry mat i j) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (h : Valid mat), ∃ r : alloc.vec.Vec Std.I64,
          find_diagonal_order mat = ok r ∧
          r.val.length = numRows mat * numCols mat ∧
          ∀ p : Nat, p < numRows mat * numCols mat →
            ∀ s : Nat, s ≤ numRows mat + numCols mat - 2 →
              diagStart mat s ≤ p → p < diagStart mat s + diagLen mat s →
                ∃ i j : Nat,
                  i < numRows mat ∧ j < numCols mat ∧ i + j = s ∧
                    outGet? r p = some (entry mat i j)) := by
    sorry

  end AegisSpec.FindDiagonalOrder
