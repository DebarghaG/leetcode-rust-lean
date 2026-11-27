import Aegis.NumSubmat.Code.Funs

/-!
# Specifications of `Aegis.NumSubmat.num_submat`

LeetCode problem `count-submatrices-with-all-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumSubmat

  def rows (mat : Slice (alloc.vec.Vec Std.I64)) : List (List Int) :=
    mat.val.map (fun row => row.val)

  def entry (mat : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : Option Int :=
    (mat.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))

  def rowLen (mat : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Option Nat :=
    (mat.val[i]?).map (fun row => row.val.length)

  def IsBitMatrix (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Prop :=
    mat.val.length = m ∧
      (∀ i, i < m → rowLen mat i = some n) ∧
      (∀ i j, i < m → j < n → entry mat i j = some 0 ∨ entry mat i j = some 1)

  def boxAllOnes (mat : Slice (alloc.vec.Vec Std.I64)) (i k j l : Nat) : Prop :=
    ∀ p, i ≤ p → p < k → ∀ q, j ≤ q → q < l → entry mat p q = some 1

  def boxes (m n : Nat) : Finset ((Nat × Nat) × (Nat × Nat)) :=
    ((Finset.range (m + 1)).product (Finset.range (m + 1))).product
      ((Finset.range (n + 1)).product (Finset.range (n + 1)))

  noncomputable def countAllOnesSubmat (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat := by
    classical
    exact ((boxes m n).filter
      (fun q => q.1.1 < q.1.2 ∧ q.2.1 < q.2.2 ∧
        boxAllOnes mat q.1.1 q.1.2 q.2.1 q.2.2)).card

  noncomputable def countOnes (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat) : Nat := by
    classical
    exact (((Finset.range m).product (Finset.range n)).filter
      (fun p => entry mat p.1 p.2 = some 1)).card

  def tri (k : Nat) : Nat :=
    k * (k + 1) / 2

  def numRects (m n : Nat) : Nat :=
    tri m * tri n

  def width (rs : List (List Int)) : Nat :=
    (rs.map List.length).foldr max 0

  def transposeRows (rs : List (List Int)) : List (List Int) :=
    (List.range (width rs)).map (fun j => rs.map (fun r => r.getD j 0))

  def revRows (rs : List (List Int)) : List (List Int) :=
    rs.reverse

  def revCols (rs : List (List Int)) : List (List Int) :=
    rs.map List.reverse

  def deleteRowAt (k : Nat) (rs : List (List Int)) : List (List Int) :=
    rs.take k ++ rs.drop (k + 1)

  def deleteColAt (l : Nat) (rs : List (List Int)) : List (List Int) :=
    rs.map (fun r => r.take l ++ r.drop (l + 1))

  def takeCols (l : Nat) (rs : List (List Int)) : List (List Int) :=
    rs.map (fun r => r.take l)

  def dropCols (l : Nat) (rs : List (List Int)) : List (List Int) :=
    rs.map (fun r => r.drop l)

  /-- The function returns a result r, and r equals the number of quadruples (i, k, j, l) of integers such that 0 <= i < k <= m, 0 <= j < l <= n, and for every p with i <= p < k and every q with j <= q < l, mat[p][q] = 1.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        r.val = (countAllOnesSubmat mat m n : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          r.val = (countAllOnesSubmat mat m n : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, overflow, or go out of bounds).
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r) := by
    sorry

  /-- The function returns a result r, and r >= N1, where N1 is the number of pairs (i, j) with 0 <= i < m and 0 <= j < n such that mat[i][j] = 1.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        (countOnes mat m n : Int) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          (countOnes mat m n : Int) ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r <= (m*(m+1)/2) * (n*(n+1)/2).
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        r.val ≤ (numRects m n : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          r.val ≤ (numRects m n : Int)) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if mat[i][j] = 0 for every 0 <= i < m and every 0 <= j < n.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → entry mat i j = some 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          (r.val = 0 ↔ ∀ i, i < m → ∀ j, j < n → entry mat i j = some 0)) := by
    sorry

  /-- Let mat^T be the n x m matrix with mat^T[j][i] = mat[i][j] for all 0 <= i < m and 0 <= j < n. The function returns a result r on mat, and on mat^T it returns a result r^T; moreover r = r^T.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_6 (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hT : rows matT = transposeRows (rows mat)) :
      ∃ r rT : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat matT = ok rT ∧ r.val = rT.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat matT : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hT : rows matT = transposeRows (rows mat)), ∃ r rT : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat matT = ok rT ∧ r.val = rT.val) := by
    sorry

  /-- Let rev_rows(mat) be the m x n matrix with rev_rows(mat)[i][j] = mat[m-1-i][j] for all 0 <= i < m and 0 <= j < n. The function returns a result r on mat, and on rev_rows(mat) it returns a result r'; moreover r = r'.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_7 (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hR : rows matR = revRows (rows mat)) :
      ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat matR = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat matR : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hR : rows matR = revRows (rows mat)), ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat matR = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let rev_cols(mat) be the m x n matrix with rev_cols(mat)[i][j] = mat[i][n-1-j] for all 0 <= i < m and 0 <= j < n. The function returns a result r on mat, and on rev_cols(mat) it returns a result r'; moreover r = r'.
    Preconditions: mat is a rectangular matrix with m rows and n columns: len(mat) = m, 1 <= m <= 150, and for every i with 0 <= i < m, len(mat[i]) = n, 1 <= n <= 150. For every i with 0 <= i < m and every j with 0 <= j < n, mat[i][j] is either 0 or 1 (as an integer). -/
  theorem spec_8 (mat matC : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hC : rows matC = revCols (rows mat)) :
      ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat matC = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat matC : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hC : rows matC = revCols (rows mat)), ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat matC = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The function returns a result r1 on mat1 and a result r2 on mat2; moreover r1 <= r2.
    Preconditions: mat1 and mat2 are two valid matrices with the same dimensions m x n: len(mat1) = len(mat2) = m, 1 <= m <= 150, every row of mat1 and mat2 has length n, 1 <= n <= 150, and for every 0 <= i < m and 0 <= j < n, mat1[i][j] and mat2[i][j] are either 0 or 1. Moreover, mat1[i][j] <= mat2[i][j] for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat1 : IsBitMatrix mat1 m n) (hmat2 : IsBitMatrix mat2 m n)
      (hle : ∀ i j, i < m → j < n → ∀ a b, entry mat1 i j = some a →
        entry mat2 i j = some b → a ≤ b) :
      ∃ r1 r2 : Std.I64, Aegis.NumSubmat.num_submat mat1 = ok r1 ∧
        Aegis.NumSubmat.num_submat mat2 = ok r2 ∧ r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat1 : IsBitMatrix mat1 m n) (hmat2 : IsBitMatrix mat2 m n)
        (hle : ∀ i j, i < m → j < n → ∀ a b, entry mat1 i j = some a →
          entry mat2 i j = some b → a ≤ b), ∃ r1 r2 : Std.I64, Aegis.NumSubmat.num_submat mat1 = ok r1 ∧
          Aegis.NumSubmat.num_submat mat2 = ok r2 ∧ r1.val ≤ r2.val) := by
    sorry

  /-- Let top be the k x n matrix with top[i][j] = mat[i][j] for 0 <= i < k and 0 <= j < n. Let bottom be the (m-k-1) x n matrix with bottom[i][j] = mat[k+1+i][j] for 0 <= i < m-k-1 and 0 <= j < n. The function returns a result r on mat, a result r_top on top, and a result r_bottom on bottom; moreover r = r_top + r_bottom.
    Preconditions: mat is a valid m x n matrix (as in spec_1) with m >= 3. There exists an integer k with 1 <= k <= m-2 such that mat[k][j] = 0 for all 0 <= j < n. -/
  theorem spec_10 (mat top bottom : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hm3 : 3 ≤ m) (hk1 : 1 ≤ k) (hk2 : k ≤ m - 2)
      (hk0 : ∀ j, j < n → entry mat k j = some 0)
      (htop : rows top = (rows mat).take k)
      (hbottom : rows bottom = (rows mat).drop (k + 1)) :
      ∃ r rtop rbot : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat top = ok rtop ∧
        Aegis.NumSubmat.num_submat bottom = ok rbot ∧
        r.val = rtop.val + rbot.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat top bottom : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hm3 : 3 ≤ m) (hk1 : 1 ≤ k) (hk2 : k ≤ m - 2)
        (hk0 : ∀ j, j < n → entry mat k j = some 0)
        (htop : rows top = (rows mat).take k)
        (hbottom : rows bottom = (rows mat).drop (k + 1)), ∃ r rtop rbot : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat top = ok rtop ∧
          Aegis.NumSubmat.num_submat bottom = ok rbot ∧
          r.val = rtop.val + rbot.val) := by
    sorry

  /-- Let left be the m x l matrix with left[i][j] = mat[i][j] for 0 <= i < m and 0 <= j < l. Let right be the m x (n-l-1) matrix with right[i][j] = mat[i][l+1+j] for 0 <= i < m and 0 <= j < n-l-1. The function returns a result r on mat, a result r_left on left, and a result r_right on right; moreover r = r_left + r_right.
    Preconditions: mat is a valid m x n matrix (as in spec_1) with n >= 3. There exists an integer l with 1 <= l <= n-2 such that mat[i][l] = 0 for all 0 <= i < m. -/
  theorem spec_11 (mat left right : Slice (alloc.vec.Vec Std.I64)) (m n l : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hn3 : 3 ≤ n) (hl1 : 1 ≤ l) (hl2 : l ≤ n - 2)
      (hl0 : ∀ i, i < m → entry mat i l = some 0)
      (hleft : rows left = takeCols l (rows mat))
      (hright : rows right = dropCols (l + 1) (rows mat)) :
      ∃ r rleft rright : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat left = ok rleft ∧
        Aegis.NumSubmat.num_submat right = ok rright ∧
        r.val = rleft.val + rright.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat left right : Slice (alloc.vec.Vec Std.I64)) (m n l : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hn3 : 3 ≤ n) (hl1 : 1 ≤ l) (hl2 : l ≤ n - 2)
        (hl0 : ∀ i, i < m → entry mat i l = some 0)
        (hleft : rows left = takeCols l (rows mat))
        (hright : rows right = dropCols (l + 1) (rows mat)), ∃ r rleft rright : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat left = ok rleft ∧
          Aegis.NumSubmat.num_submat right = ok rright ∧
          r.val = rleft.val + rright.val) := by
    sorry

  /-- The function returns a result r, and r >= (a*(a+1)/2) * (b*(b+1)/2).
    Preconditions: mat is a valid m x n matrix (as in spec_1). Integers a, b, i0, j0 satisfy 1 <= a <= m, 1 <= b <= n, 0 <= i0 <= m-a, 0 <= j0 <= n-b, and mat[i][j] = 1 for every i with i0 <= i < i0+a and every j with j0 <= j < j0+b. -/
  theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (m n a b i0 j0 : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (ha1 : 1 ≤ a) (ha2 : a ≤ m) (hb1 : 1 ≤ b) (hb2 : b ≤ n)
      (hi0 : i0 ≤ m - a) (hj0 : j0 ≤ n - b)
      (hbox : ∀ i, i0 ≤ i → i < i0 + a → ∀ j, j0 ≤ j → j < j0 + b →
        entry mat i j = some 1) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        (numRects a b : Int) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n a b i0 j0 : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (ha1 : 1 ≤ a) (ha2 : a ≤ m) (hb1 : 1 ≤ b) (hb2 : b ≤ n)
        (hi0 : i0 ≤ m - a) (hj0 : j0 ≤ n - b)
        (hbox : ∀ i, i0 ≤ i → i < i0 + a → ∀ j, j0 ≤ j → j < j0 + b →
          entry mat i j = some 1), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          (numRects a b : Int) ≤ r.val) := by
    sorry

  /-- Let mat' be the (m-1) x n matrix obtained by deleting row k: for 0 <= i < m-1 and 0 <= j < n, if i < k then mat'[i][j] = mat[i][j], and if i >= k then mat'[i][j] = mat[i+1][j]. The function returns a result r on mat and a result r' on mat'; moreover r = r'.
    Preconditions: mat is a valid m x n matrix (as in spec_1) with m >= 2. There exists k with (k = 0 or k = m-1) such that mat[k][j] = 0 for all 0 <= j < n. -/
  theorem spec_13 (mat mat' : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hm_ge : 2 ≤ m) (hk : k = 0 ∨ k = m - 1)
      (hk0 : ∀ j, j < n → entry mat k j = some 0)
      (hdel : rows mat' = deleteRowAt k (rows mat)) :
      ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat mat' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat mat' : Slice (alloc.vec.Vec Std.I64)) (m n k : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hm_ge : 2 ≤ m) (hk : k = 0 ∨ k = m - 1)
        (hk0 : ∀ j, j < n → entry mat k j = some 0)
        (hdel : rows mat' = deleteRowAt k (rows mat)), ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat mat' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- Let mat' be the m x (n-1) matrix obtained by deleting column l: for 0 <= i < m and 0 <= j < n-1, if j < l then mat'[i][j] = mat[i][j], and if j >= l then mat'[i][j] = mat[i][j+1]. The function returns a result r on mat and a result r' on mat'; moreover r = r'.
    Preconditions: mat is a valid m x n matrix (as in spec_1) with n >= 2. There exists l with (l = 0 or l = n-1) such that mat[i][l] = 0 for all 0 <= i < m. -/
  theorem spec_14 (mat mat' : Slice (alloc.vec.Vec Std.I64)) (m n l : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hn_ge : 2 ≤ n) (hl : l = 0 ∨ l = n - 1)
      (hl0 : ∀ i, i < m → entry mat i l = some 0)
      (hdel : rows mat' = deleteColAt l (rows mat)) :
      ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        Aegis.NumSubmat.num_submat mat' = ok r' ∧ r.val = r'.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (mat mat' : Slice (alloc.vec.Vec Std.I64)) (m n l : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hn_ge : 2 ≤ n) (hl : l = 0 ∨ l = n - 1)
        (hl0 : ∀ i, i < m → entry mat i l = some 0)
        (hdel : rows mat' = deleteColAt l (rows mat)), ∃ r r' : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          Aegis.NumSubmat.num_submat mat' = ok r' ∧ r.val = r'.val) := by
    sorry

  /-- The function returns a result r, and r = (m*(m+1)/2) * (n*(n+1)/2).
    Preconditions: mat is a valid m x n matrix (as in spec_1) and mat[i][j] = 1 for every 0 <= i < m and every 0 <= j < n. -/
  theorem spec_15 (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
      (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
      (hmat : IsBitMatrix mat m n)
      (hall : ∀ i, i < m → ∀ j, j < n → entry mat i j = some 1) :
      ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
        r.val = (numRects m n : Int) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (m n : Nat)
        (hm1 : 1 ≤ m) (hm2 : m ≤ 150) (hn1 : 1 ≤ n) (hn2 : n ≤ 150)
        (hmat : IsBitMatrix mat m n)
        (hall : ∀ i, i < m → ∀ j, j < n → entry mat i j = some 1), ∃ r : Std.I64, Aegis.NumSubmat.num_submat mat = ok r ∧
          r.val = (numRects m n : Int)) := by
    sorry

  end AegisSpec.NumSubmat
