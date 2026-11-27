import Aegis.MostFrequentPrime.Code.Funs

/-!
# Specifications of `Aegis.MostFrequentPrime.most_frequent_prime`

LeetCode problem `most-frequent-prime`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.MostFrequentPrime

  namespace AegisSpec.MostFrequentPrime

  def IsPrime (p : ℤ) : Prop := 2 ≤ p ∧ ∀ d : ℤ, 1 ≤ d → d ∣ p → d = 1 ∨ d = p

  def cells (mat : Slice (alloc.vec.Vec Std.I64)) : List (List ℤ) :=
    mat.val.map (fun row => row.val.map (fun x => x.val))

  def matHeight (c : List (List ℤ)) : ℕ := c.length

  def matWidth (c : List (List ℤ)) : ℕ :=
    match c with
    | [] => 0
    | row :: _ => row.length

  def cellAt (c : List (List ℤ)) (i j : ℕ) : ℤ := (c.getD i []).getD j 0

  def dirs : List (ℤ × ℤ) :=
    [(0, 1), (1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1)]

  abbrev InGrid (m n : ℕ) (i j : ℤ) : Prop := 0 ≤ i ∧ i < (m : ℤ) ∧ 0 ≤ j ∧ j < (n : ℤ)

  def SegInGrid (m n : ℕ) (i j : ℕ) (di dj : ℤ) (L : ℕ) : Prop :=
    2 ≤ L ∧ ∀ k : ℕ, k < L → InGrid m n ((i : ℤ) + (k : ℤ) * di) ((j : ℤ) + (k : ℤ) * dj)

  def numFrom (c : List (List ℤ)) (i j : ℕ) (di dj : ℤ) (L : ℕ) : ℤ :=
    ((List.range L).map (fun k =>
        cellAt c (Int.toNat ((i : ℤ) + (k : ℤ) * di))
          (Int.toNat ((j : ℤ) + (k : ℤ) * dj)))).foldl
      (fun acc d => acc * 10 + d) 0

  def extendSegments (c : List (List ℤ)) (m n : ℕ) : ℕ → ℤ → ℤ → ℤ → ℤ → ℤ → List ℤ
    | 0, _, _, _, _, _ => []
    | fuel + 1, i, j, di, dj, acc =>
      if InGrid m n (i + di) (j + dj) then
        (let acc' : ℤ := acc * 10 + cellAt c (Int.toNat (i + di)) (Int.toNat (j + dj))
         acc' :: extendSegments c m n fuel (i + di) (j + dj) di dj acc')
      else []

  def generated (c : List (List ℤ)) (m n : ℕ) : List ℤ :=
    (List.range m).flatMap (fun (i : ℕ) =>
      (List.range n).flatMap (fun (j : ℕ) =>
        dirs.flatMap (fun d =>
          extendSegments c m n (m + n + 2) (i : ℤ) (j : ℤ) d.1 d.2 (cellAt c i j))))

  def freq (s : List ℤ) (p : ℤ) : ℕ := s.countP (fun x => x == p)

  def rowSegments (c : List (List ℤ)) (n : ℕ) : List ℤ := generated c 1 n

  def colSegments (c : List (List ℤ)) (m : ℕ) : List ℤ := generated c m 1

  def IsBest (s : List ℤ) (r : ℤ) : Prop :=
    (r = -1 ∧ ∀ p : ℤ, IsPrime p → 10 < p → freq s p = 0) ∨
      (10 < r ∧ IsPrime r ∧ 0 < freq s r ∧
        ∀ q : ℤ, IsPrime q → 10 < q → 0 < freq s q →
          freq s q < freq s r ∨ (freq s q = freq s r ∧ q ≤ r))

  def IsMaxPrimeOfPair (A B r : ℤ) : Prop :=
    (r = -1 ∧ ¬ IsPrime A ∧ ¬ IsPrime B) ∨
      (IsPrime r ∧ (r = A ∨ r = B) ∧ ∀ p : ℤ, (p = A ∨ p = B) → IsPrime p → p ≤ r)

  def transposeCells (c : List (List ℤ)) : List (List ℤ) :=
    (List.range (matWidth c)).map (fun j => c.map (fun row => row.getD j 0))

  def hflipCells (c : List (List ℤ)) : List (List ℤ) := c.map (fun row => row.reverse)

  def vflipCells (c : List (List ℤ)) : List (List ℤ) := c.reverse

  def rot180Cells (c : List (List ℤ)) : List (List ℤ) := (hflipCells c).reverse

  /-- Let D = {(0,1),(1,1),(1,0),(1,-1),(0,-1),(-1,-1),(-1,0),(-1,1)}. For any cell (i,j) with 0 <= i < m and 0 <= j < n, any direction (di,dj) in D, and any integer L >= 2 such that for all k with 0 <= k < L, the cell (i + k*di, j + k*dj) satisfies 0 <= i + k*di < m and 0 <= j + k*dj < n, define the number formed as N(i,j,di,dj,L) = sum_{k=0}^{L-1} mat[i + k*di][j + k*dj] * 10^{L-1-k}. Let Generated(mat) be the multiset containing exactly one occurrence of N(i,j,di,dj,L) for each valid choice of (i,j), (di,dj), and L. For any integer p, let freq(p) be the number of occurrences of p in Generated(mat). The function returns Ok r such that either (r = -1 and there is no prime p > 10 with freq(p) > 0), or (r > 10, r is prime, freq(r) > 0, and for every prime q > 10 with freq(q) > 0, either freq(q) < freq(r) or (freq(q) = freq(r) and q <= r)).
    Preconditions: mat is a non-empty 2D array of 64-bit integers. Let m = len(mat) and n = len(mat[0]). We assume 1 <= m <= 6, 1 <= n <= 6, and for all i with 0 <= i < m, len(mat[i]) = n. Also, for all i with 0 <= i < m and j with 0 <= j < n, 1 <= mat[i][j] <= 9. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9) :
      ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (generated (cells mat) m n) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9), ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (generated (cells mat) m n) r.val) := by
    sorry

  /-- The function returns a result of the form Ok r for some 64-bit integer r. (It does not return Err, i.e., it does not fail due to overflow, out-of-bounds access, or panic.)
    Preconditions: mat is a non-empty 2D array of 64-bit integers. Let m = len(mat) and n = len(mat[0]). We assume 1 <= m <= 6, 1 <= n <= 6, and for all i with 0 <= i < m, len(mat[i]) = n. Also, for all i with 0 <= i < m and j with 0 <= j < n, 1 <= mat[i][j] <= 9. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9) :
      ∃ r : Std.I64, most_frequent_prime mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9), ∃ r : Std.I64, most_frequent_prime mat = ok r) := by
    sorry

  /-- If the function returns Ok r, then either r = -1 or (11 <= r <= 999999).
    Preconditions: mat is a non-empty 2D array of 64-bit integers. Let m = len(mat) and n = len(mat[0]). We assume 1 <= m <= 6, 1 <= n <= 6, and for all i with 0 <= i < m, len(mat[i]) = n. Also, for all i with 0 <= i < m and j with 0 <= j < n, 1 <= mat[i][j] <= 9. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9) :
      ∀ r : Std.I64, most_frequent_prime mat = ok r →
        (r.val = -1 ∨ (11 ≤ r.val ∧ r.val ≤ 999999)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9), ∀ r : Std.I64, most_frequent_prime mat = ok r →
          (r.val = -1 ∨ (11 ≤ r.val ∧ r.val ≤ 999999))) := by
    sorry

  /-- The function returns Ok (-1).
    Preconditions: mat is a 1x1 matrix: m = len(mat) = 1, n = len(mat[0]) = 1, and 1 <= mat[0][0] <= 9. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : m = 1) (hn1 : n = 1)
      (hcell : 1 ≤ cellAt (cells mat) 0 0 ∧ cellAt (cells mat) 0 0 ≤ 9) :
      most_frequent_prime mat = ok (-1)#i64 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : m = 1) (hn1 : n = 1)
        (hcell : 1 ≤ cellAt (cells mat) 0 0 ∧ cellAt (cells mat) 0 0 ≤ 9), most_frequent_prime mat = ok (-1)#i64) := by
    sorry

  /-- The function returns Ok 11.
    Preconditions: mat is a non-empty rectangular matrix with m = len(mat), n = len(mat[0]), 1 <= m <= 6, 1 <= n <= 6, all entries are 1, and m * n >= 2 (i.e., the matrix is not 1x1). -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hall : ∀ row ∈ cells mat, ∀ x ∈ row, x = 1)
      (hge : 2 ≤ m * n) :
      most_frequent_prime mat = ok 11#i64 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hall : ∀ row ∈ cells mat, ∀ x ∈ row, x = 1)
        (hge : 2 ≤ m * n), most_frequent_prime mat = ok 11#i64) := by
    sorry

  /-- Let A = 10*a + b and B = 10*b + a. The function returns Ok r where r = -1 if neither A nor B is prime, and otherwise r = max({p in {A,B} : p is prime}).
    Preconditions: mat is a 1x2 matrix: m = len(mat) = 1, n = len(mat[0]) = 2, and a = mat[0][0], b = mat[0][1] are integers with 1 <= a,b <= 9. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (a b : ℤ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : m = 1) (hn2 : n = 2)
      (ha : a = cellAt (cells mat) 0 0) (hb : b = cellAt (cells mat) 0 1)
      (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb1 : 1 ≤ b) (hb9 : b ≤ 9) :
      ∃ r : Std.I64,
        most_frequent_prime mat = ok r ∧ IsMaxPrimeOfPair (10 * a + b) (10 * b + a) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ) (a b : ℤ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : m = 1) (hn2 : n = 2)
        (ha : a = cellAt (cells mat) 0 0) (hb : b = cellAt (cells mat) 0 1)
        (ha1 : 1 ≤ a) (ha9 : a ≤ 9) (hb1 : 1 ≤ b) (hb9 : b ≤ 9), ∃ r : Std.I64,
          most_frequent_prime mat = ok r ∧ IsMaxPrimeOfPair (10 * a + b) (10 * b + a) r.val) := by
    sorry

  /-- most_frequent_prime(mat) = most_frequent_prime(matT). That is, if the function returns Ok r on mat, it returns Ok r on matT, and if it fails on one, it fails on the other.
    Preconditions: mat is a rectangular matrix with m = len(mat), n = len(mat[0]), 1 <= m <= 6, 1 <= n <= 6, and all entries in 1..9. Let matT be the n x m matrix defined by matT[j][i] = mat[i][j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
      (hT : cells matT = transposeCells (cells mat)) :
      most_frequent_prime mat = most_frequent_prime matT := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
        (hT : cells matT = transposeCells (cells mat)), most_frequent_prime mat = most_frequent_prime matT) := by
    sorry

  /-- most_frequent_prime(mat) = most_frequent_prime(matH).
    Preconditions: mat is a rectangular matrix with m = len(mat), n = len(mat[0]), 1 <= m <= 6, 1 <= n <= 6, and all entries in 1..9. Let matH be the matrix defined by matH[i][j] = mat[i][n-1-j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (mat matH : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
      (hH : cells matH = hflipCells (cells mat)) :
      most_frequent_prime mat = most_frequent_prime matH := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat matH : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
        (hH : cells matH = hflipCells (cells mat)), most_frequent_prime mat = most_frequent_prime matH) := by
    sorry

  /-- most_frequent_prime(mat) = most_frequent_prime(matV).
    Preconditions: mat is a rectangular matrix with m = len(mat), n = len(mat[0]), 1 <= m <= 6, 1 <= n <= 6, and all entries in 1..9. Let matV be the matrix defined by matV[i][j] = mat[m-1-i][j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (mat matV : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
      (hV : cells matV = vflipCells (cells mat)) :
      most_frequent_prime mat = most_frequent_prime matV := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat matV : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
        (hV : cells matV = vflipCells (cells mat)), most_frequent_prime mat = most_frequent_prime matV) := by
    sorry

  /-- most_frequent_prime(mat) = most_frequent_prime(matR).
    Preconditions: mat is a rectangular matrix with m = len(mat), n = len(mat[0]), 1 <= m <= 6, 1 <= n <= 6, and all entries in 1..9. Let matR be the matrix defined by matR[i][j] = mat[m-1-i][n-1-j] for 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
      (hR : cells matR = rot180Cells (cells mat)) :
      most_frequent_prime mat = most_frequent_prime matR := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9)
        (hR : cells matR = rot180Cells (cells mat)), most_frequent_prime mat = most_frequent_prime matR) := by
    sorry

  /-- Let S be the multiset of all numbers formed by taking any contiguous segment of the row mat[0] of length L >= 2, in either left-to-right or right-to-left order. That is, for every j with 0 <= j < n and L >= 2 with j+L <= n, include the number formed by mat[0][j], mat[0][j+1], ..., mat[0][j+L-1] (most significant digit first); and for every j with 0 <= j < n and L >= 2 with j-L+1 >= 0, include the number formed by mat[0][j], mat[0][j-1], ..., mat[0][j-L+1] (most significant digit first). Then the function returns Ok r where either r = -1 and no prime >10 appears in S, or r > 10 is prime, appears in S, and for every prime q > 10 appearing in S, either freq_S(q) < freq_S(r) or (freq_S(q) = freq_S(r) and q <= r), where freq_S denotes multiplicity in S.
    Preconditions: mat is a 1 x n matrix: m = len(mat) = 1, n = len(mat[0]), 1 <= n <= 6, and all entries in 1..9. -/
  theorem spec_11 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : m = 1) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9) :
      ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (rowSegments (cells mat) n) r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : m = 1) (hn1 : 1 ≤ n) (hn6 : n ≤ 6)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9), ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (rowSegments (cells mat) n) r.val) := by
    sorry

  /-- Let S be the multiset of all numbers formed by taking any contiguous segment of the column (i.e., the sequence mat[0][0], mat[1][0], ..., mat[m-1][0]) of length L >= 2, in either top-to-bottom or bottom-to-top order. That is, for every i with 0 <= i < m and L >= 2 with i+L <= m, include the number formed by mat[i][0], mat[i+1][0], ..., mat[i+L-1][0] (most significant digit first); and for every i with 0 <= i < m and L >= 2 with i-L+1 >= 0, include the number formed by mat[i][0], mat[i-1][0], ..., mat[i-L+1][0] (most significant digit first). Then the function returns Ok r where either r = -1 and no prime >10 appears in S, or r > 10 is prime, appears in S, and for every prime q > 10 appearing in S, either freq_S(q) < freq_S(r) or (freq_S(q) = freq_S(r) and q <= r), where freq_S denotes multiplicity in S.
    Preconditions: mat is an m x 1 matrix: m = len(mat), n = len(mat[0]) = 1, 1 <= m <= 6, and all entries in 1..9. -/
  theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
      (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
      (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : n = 1)
      (hrows : ∀ row ∈ cells mat, row.length = n)
      (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9) :
      ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (colSegments (cells mat) m) r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : ℕ)
        (hm : m = matHeight (cells mat)) (hn : n = matWidth (cells mat))
        (hm1 : 1 ≤ m) (hm6 : m ≤ 6) (hn1 : n = 1)
        (hrows : ∀ row ∈ cells mat, row.length = n)
        (hdigits : ∀ row ∈ cells mat, ∀ x ∈ row, 1 ≤ x ∧ x ≤ 9), ∃ r : Std.I64, most_frequent_prime mat = ok r ∧ IsBest (colSegments (cells mat) m) r.val) := by
    sorry

  end AegisSpec.MostFrequentPrime
