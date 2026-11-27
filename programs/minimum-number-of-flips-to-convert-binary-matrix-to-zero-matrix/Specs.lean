import Aegis.MinFlips.Code.Funs

/-!
# Specifications of `Aegis.MinFlips.min_flips`

LeetCode problem `minimum-number-of-flips-to-convert-binary-matrix-to-zero-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinFlips

  namespace AegisSpec.MinFlips

  abbrev Grid := List (List ℤ)

  def grid (mat : Slice (alloc.vec.Vec I64)) : Grid :=
    mat.val.map fun row => row.val.map fun x => x.val

  def entry (M : Grid) (i j : ℕ) : ℤ := (M.getD i []).getD j 0

  abbrev Neighbour (i j a b : ℕ) : Prop := (i - a) + (a - i) + (j - b) + (b - j) ≤ 1

  abbrev cells (m n : ℕ) : List (ℕ × ℕ) := (List.range m).product (List.range n)

  def flipCount (moves : List (ℕ × ℕ)) (i j : ℕ) : ℕ :=
    (moves.filter fun p => decide (Neighbour i j p.1 p.2)).length

  def IsMoveSolution (M : Grid) (m n : ℕ) (moves : List (ℕ × ℕ)) : Prop :=
    (∀ p ∈ moves, p.1 < m ∧ p.2 < n) ∧
      ∀ i j : ℕ, i < m → j < n →
        ∃ t : ℤ, (flipCount moves i j : ℤ) = entry M i j + 2 * t

  def HasKMoveSolution (M : Grid) (m n k : ℕ) : Prop :=
    ∃ moves : List (ℕ × ℕ), IsMoveSolution M m n moves ∧ moves.length = k

  def AllZero (M : Grid) : Prop := ∀ r ∈ M, ∀ x ∈ r, x = 0

  def Binary (M : Grid) : Prop := ∀ r ∈ M, ∀ x ∈ r, x = 0 ∨ x = 1

  def flipAt (M : Grid) (a b : ℕ) : Grid :=
    M.mapIdx fun i row => row.mapIdx fun j x => if Neighbour i j a b then 1 - x else x

  def transpose (M : Grid) : Grid :=
    (List.range (M.getD 0 []).length).map fun j =>
      (List.range M.length).map fun i => entry M i j

  def reverseRows (M : Grid) : Grid := M.map List.reverse

  def reverseRowOrder (M : Grid) : Grid := M.reverse

  def nearSum (x : Grid) (m n i j : ℕ) : ℤ :=
    List.sum <| ((cells m n).filter fun p => decide (Neighbour i j p.1 p.2)).map
      fun p => entry x p.1 p.2

  def IsPreimage (M x : Grid) (m n : ℕ) : Prop :=
    x.length = m ∧ (∀ r ∈ x, r.length = n) ∧ Binary x ∧
      ∀ i j : ℕ, i < m → j < n → ∃ t : ℤ, entry M i j = nearSum x m n i j + 2 * t

  def countOnes (M : Grid) : ℕ :=
    (M.map fun r => (r.filter fun x => decide (x = 1)).length).sum

  /-- For every such mat, min_flips(mat) returns a result r. A legal move is a pair (a,b) with 0 <= a < m and 0 <= b < n; it toggles every cell (i,j) with 0 <= i < m, 0 <= j < n and |i-a|+|j-b| <= 1. A k-move solution of mat is a list of k legal moves whose application in order leaves every cell equal to 0; equivalently, for every cell (i,j), the number of listed moves (a,b) with |i-a|+|j-b| <= 1 is congruent to mat[i][j] modulo 2. Then either r = -1 and there is no integer k >= 0 for which a k-move solution exists, or 0 <= r and there exists an r-move solution, and for every integer k with 0 <= k < r no k-move solution exists.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      ∃ r : I64, min_flips mat = ok r ∧
        ((r.val = -1 ∧ ∀ k : ℕ, ¬ HasKMoveSolution (grid mat) m n k) ∨
          (0 ≤ r.val ∧ HasKMoveSolution (grid mat) m n r.val.toNat ∧
            ∀ k : ℕ, k < r.val.toNat → ¬ HasKMoveSolution (grid mat) m n k)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), ∃ r : I64, min_flips mat = ok r ∧
          ((r.val = -1 ∧ ∀ k : ℕ, ¬ HasKMoveSolution (grid mat) m n k) ∨
            (0 ≤ r.val ∧ HasKMoveSolution (grid mat) m n r.val.toNat ∧
              ∀ k : ℕ, k < r.val.toNat → ¬ HasKMoveSolution (grid mat) m n k))) := by
    sorry

  /-- For every mat satisfying the preconditions, min_flips(mat) returns a result r; in particular, it does not fail, panic, or overflow, and r is a 64-bit integer.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      ∃ r : I64, min_flips mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), ∃ r : I64, min_flips mat = ok r) := by
    sorry

  /-- For every mat satisfying the preconditions, min_flips(mat) returns a result r and either r = -1 or 0 <= r <= m*n (where m = len(mat) and n is the common row length); in particular r <= 9.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      ∃ r : I64, min_flips mat = ok r ∧ (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ ((m * n : ℕ) : ℤ))) :=
    by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), ∃ r : I64, min_flips mat = ok r ∧ (r.val = -1 ∨ (0 ≤ r.val ∧ r.val ≤ ((m * n : ℕ) : ℤ)))) := by
    sorry

  /-- If every entry of mat is 0, then min_flips(mat) returns 0.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and every entry mat[i][j] is 0. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hzero : AllZero (grid mat)) :
      ∃ r : I64, min_flips mat = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hzero : AllZero (grid mat)), ∃ r : I64, min_flips mat = ok r ∧ r.val = 0) := by
    sorry

  /-- If m = 1 and n = 1, then min_flips(mat) returns mat[0][0].
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = 1 and n = 1. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm1' : m = 1) (hn1' : n = 1) :
      ∃ r : I64, min_flips mat = ok r ∧ r.val = entry (grid mat) 0 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm1' : m = 1) (hn1' : n = 1), ∃ r : I64, min_flips mat = ok r ∧ r.val = entry (grid mat) 0 0) := by
    sorry

  /-- If mat is the 2 x 2 matrix all of whose entries are 1, then min_flips(mat) returns 4.
    Preconditions: Let m = len(mat) and let n be the common length of the rows. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = n = 2 and mat[i][j] = 1 for every 0 <= i < 2 and 0 <= j < 2. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm2' : m = 2) (hn2' : n = 2)
      (hones : ∀ i j : ℕ, i < 2 → j < 2 → entry (grid mat) i j = 1) :
      ∃ r : I64, min_flips mat = ok r ∧ r.val = 4 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm2' : m = 2) (hn2' : n = 2)
        (hones : ∀ i j : ℕ, i < 2 → j < 2 → entry (grid mat) i j = 1), ∃ r : I64, min_flips mat = ok r ∧ r.val = 4) := by
    sorry

  /-- If mat is the 3 x 3 matrix all of whose entries are 1, then min_flips(mat) returns 5.
    Preconditions: Let m = len(mat) and let n be the common length of the rows. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = n = 3 and mat[i][j] = 1 for every 0 <= i < 3 and 0 <= j < 3. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm3' : m = 3) (hn3' : n = 3)
      (hones : ∀ i j : ℕ, i < 3 → j < 3 → entry (grid mat) i j = 1) :
      ∃ r : I64, min_flips mat = ok r ∧ r.val = 5 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm3' : m = 3) (hn3' : n = 3)
        (hones : ∀ i j : ℕ, i < 3 → j < 3 → entry (grid mat) i j = 1), ∃ r : I64, min_flips mat = ok r ∧ r.val = 5) := by
    sorry

  /-- For this mat, min_flips(mat) returns -1.
    Preconditions: Let m = len(mat) and let n be the common length of the rows. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = 2, n = 3, mat[0][0] = 1, mat[1][0] = 1, and mat[i][j] = 0 for every (i,j) other than (0,0) and (1,0). -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm2' : m = 2) (hn3' : n = 3)
      (hentries : ∀ i j : ℕ, i < 2 → j < 3 →
        (entry (grid mat) i j = 1 ↔ ((i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0)))) :
      ∃ r : I64, min_flips mat = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm2' : m = 2) (hn3' : n = 3)
        (hentries : ∀ i j : ℕ, i < 2 → j < 3 →
          (entry (grid mat) i j = 1 ↔ ((i = 0 ∧ j = 0) ∨ (i = 1 ∧ j = 0)))), ∃ r : I64, min_flips mat = ok r ∧ r.val = -1) := by
    sorry

  /-- If m = 1 and n = 2, then: (a) if mat[0][0] = 0 and mat[0][1] = 0, min_flips(mat) returns 0; (b) if mat[0][0] = 1 and mat[0][1] = 1, min_flips(mat) returns 1; (c) if exactly one of mat[0][0], mat[0][1] is 1, min_flips(mat) returns -1.
    Preconditions: Let m = len(mat) and let n be the common length of the rows. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = 1 and n = 2. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm1' : m = 1) (hn2' : n = 2) :
      ((entry (grid mat) 0 0 = 0 ∧ entry (grid mat) 0 1 = 0) →
          ∃ r : I64, min_flips mat = ok r ∧ r.val = 0) ∧
        ((entry (grid mat) 0 0 = 1 ∧ entry (grid mat) 0 1 = 1) →
          ∃ r : I64, min_flips mat = ok r ∧ r.val = 1) ∧
        (((entry (grid mat) 0 0 = 1 ∧ entry (grid mat) 0 1 = 0) ∨
            (entry (grid mat) 0 0 = 0 ∧ entry (grid mat) 0 1 = 1)) →
          ∃ r : I64, min_flips mat = ok r ∧ r.val = -1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm1' : m = 1) (hn2' : n = 2), ((entry (grid mat) 0 0 = 0 ∧ entry (grid mat) 0 1 = 0) →
            ∃ r : I64, min_flips mat = ok r ∧ r.val = 0) ∧
          ((entry (grid mat) 0 0 = 1 ∧ entry (grid mat) 0 1 = 1) →
            ∃ r : I64, min_flips mat = ok r ∧ r.val = 1) ∧
          (((entry (grid mat) 0 0 = 1 ∧ entry (grid mat) 0 1 = 0) ∨
              (entry (grid mat) 0 0 = 0 ∧ entry (grid mat) 0 1 = 1)) →
            ∃ r : I64, min_flips mat = ok r ∧ r.val = -1)) := by
    sorry

  /-- For every mat satisfying the preconditions, let matT be the n x m matrix defined by matT[j][i] = mat[i][j] for all 0 <= i < m and 0 <= j < n. Then min_flips(mat) and min_flips(matT) both return results r and r', and r = r'.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_10 (mat matT : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hT : grid matT = transpose (grid mat)) :
      ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matT = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat matT : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hT : grid matT = transpose (grid mat)), ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matT = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- For every mat satisfying the preconditions, let matR be the m x n matrix defined by matR[i][j] = mat[i][n-1-j] for all 0 <= i < m and 0 <= j < n (reversing the order of cells in each row). Then min_flips(mat) and min_flips(matR) both return results r and r', and r = r'.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_11 (mat matR : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hR : grid matR = reverseRows (grid mat)) :
      ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matR = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat matR : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hR : grid matR = reverseRows (grid mat)), ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matR = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- For every mat satisfying the preconditions, let matV be the m x n matrix defined by matV[i][j] = mat[m-1-i][j] for all 0 <= i < m and 0 <= j < n (reversing the order of the rows). Then min_flips(mat) and min_flips(matV) both return results r and r', and r = r'.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_12 (mat matV : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hV : grid matV = reverseRowOrder (grid mat)) :
      ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matV = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat matV : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hV : grid matV = reverseRowOrder (grid mat)), ∃ r r' : I64, min_flips mat = ok r ∧ min_flips matV = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- For every mat satisfying the preconditions, min_flips(mat) returns a result r, and r = 0 if and only if every entry mat[i][j] is 0.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_13 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      ∃ r : I64, min_flips mat = ok r ∧ (r.val = 0 ↔ AllZero (grid mat)) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), ∃ r : I64, min_flips mat = ok r ∧ (r.val = 0 ↔ AllZero (grid mat))) := by
    sorry

  /-- For every mat satisfying the preconditions and every legal cell (a,b) with 0 <= a < m and 0 <= b < n, let mat2 be the m x n matrix obtained from mat by toggling exactly the cells (i,j) with |i-a|+|j-b| <= 1 (i.e., applying one legal flip at (a,b)). Let r = min_flips(mat) and r2 = min_flips(mat2). Then either r = -1 and r2 = -1, or both r and r2 are nonnegative and |r - r2| <= 1.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_14 (mat mat2 : Slice (alloc.vec.Vec I64)) (m n a b : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (ha : a < m) (hb : b < n)
      (h2 : grid mat2 = flipAt (grid mat) a b) :
      ∃ r r2 : I64, min_flips mat = ok r ∧ min_flips mat2 = ok r2 ∧
        ((r.val = -1 ∧ r2.val = -1) ∨
          (0 ≤ r.val ∧ 0 ≤ r2.val ∧ r.val - r2.val ≤ 1 ∧ r2.val - r.val ≤ 1)) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (mat mat2 : Slice (alloc.vec.Vec I64)) (m n a b : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (ha : a < m) (hb : b < n)
        (h2 : grid mat2 = flipAt (grid mat) a b), ∃ r r2 : I64, min_flips mat = ok r ∧ min_flips mat2 = ok r2 ∧
          ((r.val = -1 ∧ r2.val = -1) ∨
            (0 ≤ r.val ∧ 0 ≤ r2.val ∧ r.val - r2.val ≤ 1 ∧ r2.val - r.val ≤ 1))) := by
    sorry

  /-- For every mat satisfying the preconditions, min_flips(mat) returns -1 if and only if there is no m x n matrix x with every x[i][j] in {0,1} such that for every cell (i,j) with 0 <= i < m and 0 <= j < n, mat[i][j] is congruent modulo 2 to the sum of x[a][b] over all valid cells (a,b) with |i-a|+|j-b| <= 1.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_15 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      ∃ r : I64, min_flips mat = ok r ∧
        (r.val = -1 ↔ ¬ ∃ x : Grid, IsPreimage (grid mat) x m n) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), ∃ r : I64, min_flips mat = ok r ∧
          (r.val = -1 ↔ ¬ ∃ x : Grid, IsPreimage (grid mat) x m n)) := by
    sorry

  /-- For every mat satisfying the preconditions, if min_flips(mat) = -1, then (m,n) is one of (1,2), (2,1), (2,3), or (3,2). Equivalently, if (m,n) is not one of those four ordered pairs, then min_flips(mat) is nonnegative for every such mat.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; and for every i,j with 0 <= i < m and 0 <= j < n, mat[i][j] is either 0 or 1. -/
  theorem spec_16 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) :
      (∀ r : I64, min_flips mat = ok r → r.val = -1 →
          (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2)) ∧
        (¬ ((m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2)) →
          ∀ r : I64, min_flips mat = ok r → 0 ≤ r.val) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)), (∀ r : I64, min_flips mat = ok r → r.val = -1 →
            (m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2)) ∧
          (¬ ((m = 1 ∧ n = 2) ∨ (m = 2 ∧ n = 1) ∨ (m = 2 ∧ n = 3) ∨ (m = 3 ∧ n = 2)) →
            ∀ r : I64, min_flips mat = ok r → 0 ≤ r.val)) := by
    sorry

  /-- For every 3x3 binary matrix mat, there is exactly one 3x3 binary matrix x such that for every cell (i,j), mat[i][j] is congruent modulo 2 to the sum of x[a][b] over all valid cells (a,b) with |i-a|+|j-b| <= 1; and min_flips(mat) is the number of entries of x equal to 1.
    Preconditions: Let m = len(mat) and let n be the common length of the rows, so mat is an m x n matrix. 1 <= m <= 3, 1 <= n <= 3; every row mat[i] has length n; every entry mat[i][j] is either 0 or 1; and m = 3 and n = 3. -/
  theorem spec_17 (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
      (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
      (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
      (hbin : Binary (grid mat)) (hm3' : m = 3) (hn3' : n = 3) :
      ∃ x : Grid, IsPreimage (grid mat) x m n ∧
        (∀ x' : Grid, IsPreimage (grid mat) x' m n → x' = x) ∧
          ∃ r : I64, min_flips mat = ok r ∧ r.val = ((countOnes x : ℕ) : ℤ) := by
    sorry

  theorem spec_17_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : ℕ)
        (hm : (grid mat).length = m) (hm1 : 1 ≤ m) (hm3 : m ≤ 3)
        (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (hrows : ∀ r ∈ grid mat, r.length = n)
        (hbin : Binary (grid mat)) (hm3' : m = 3) (hn3' : n = 3), ∃ x : Grid, IsPreimage (grid mat) x m n ∧
          (∀ x' : Grid, IsPreimage (grid mat) x' m n → x' = x) ∧
            ∃ r : I64, min_flips mat = ok r ∧ r.val = ((countOnes x : ℕ) : ℤ)) := by
    sorry

  end AegisSpec.MinFlips
