import Aegis.UpdateMatrix.Code.Funs

/-!
# Specifications of `Aegis.UpdateMatrix.update_matrix`

LeetCode problem `01-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.UpdateMatrix

  namespace AegisSpec.UpdateMatrix

  abbrev Matrix := List (alloc.vec.Vec I64)

  abbrev OutMat := alloc.vec.Vec (alloc.vec.Vec I64)

  def rowEntries (v : alloc.vec.Vec I64) : List Int := v.val.map (fun x => x.val)

  def matrixEntries (rows : Matrix) : List (List Int) := rows.map rowEntries

  def rowOf (rows : Matrix) (i : Nat) : List Int := (matrixEntries rows)[i]?.getD []

  def cellOf (rows : Matrix) (i j : Nat) : Int := (rowOf rows i)[j]?.getD 0

  def dist (i j a b : Nat) : Int := |(i : Int) - (a : Int)| + |(j : Int) - (b : Int)|

  def zeroCells (rows : Matrix) (m n : Nat) : List (Nat × Nat) :=
    ((List.range m).product (List.range n)).filter (fun p => cellOf rows p.1 p.2 = 0)

  def minDistToZero (rows : Matrix) (m n i j : Nat) : Option Int :=
    ((zeroCells rows m n).map (fun p => dist i j p.1 p.2)).min?

  def gridNeighbours (m n i j : Nat) : List (Nat × Nat) :=
    ([(i + 1, j), (i, j + 1)] ++ (if 0 < i then [(i - 1, j)] else [])
        ++ (if 0 < j then [(i, j - 1)] else [])).filter (fun p => p.1 < m ∧ p.2 < n)

  /-- Whenever update_matrix(mat) returns a result r, r has dimensions m by n (len(r) = m and len(r[i]) = n for every 0 <= i < m), and for every cell (i,j) with 0 <= i < m and 0 <= j < n, r[i][j] equals the integer minimum of the set { |i-a| + |j-b| : 0 <= a < m, 0 <= b < n, mat[a][b] = 0 }.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        r.val.length = m ∧ (∀ i, i < m → (rowOf r.val i).length = n) ∧
          ∀ i j, i < m → j < n → minDistToZero mat.val m n i j = some (cellOf r.val i j) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          r.val.length = m ∧ (∀ i, i < m → (rowOf r.val i).length = n) ∧
            ∀ i j, i < m → j < n → minDistToZero mat.val m n i j = some (cellOf r.val i j)) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, len(r) = len(mat), and for every 0 <= i < len(mat), len(r[i]) = len(mat[i]). Thus, since mat is m by n, r is also m by n.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        r.val.length = mat.val.length ∧
          ∀ i, i < mat.val.length → (rowOf r.val i).length = (rowOf mat.val i).length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          r.val.length = mat.val.length ∧
            ∀ i, i < mat.val.length → (rowOf r.val i).length = (rowOf mat.val i).length) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n, 0 <= r[i][j].
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n → 0 ≤ cellOf r.val i j := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → 0 ≤ cellOf r.val i j) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] <= (m - 1) + (n - 1).
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n →
          cellOf r.val i j ≤ ((m - 1 : Nat) : Int) + ((n - 1 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n →
            cellOf r.val i j ≤ ((m - 1 : Nat) : Int) + ((n - 1 : Nat) : Int)) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = 0 if and only if mat[i][j] = 0.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n → (cellOf r.val i j = 0 ↔ cellOf mat.val i j = 0) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → (cellOf r.val i j = 0 ↔ cellOf mat.val i j = 0)) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n, there exist a,b with 0 <= a < m, 0 <= b < n, mat[a][b] = 0, and r[i][j] = |i-a| + |j-b|.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n →
          ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0 ∧ cellOf r.val i j = dist i j a b := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n →
            ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0 ∧ cellOf r.val i j = dist i j a b) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m, 0 <= j < n, and every 0 <= a < m, 0 <= b < n with mat[a][b] = 0, r[i][j] <= |i-a| + |j-b|.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n → ∀ a b, a < m → b < n → cellOf mat.val a b = 0 →
          cellOf r.val i j ≤ dist i j a b := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → ∀ a b, a < m → b < n → cellOf mat.val a b = 0 →
            cellOf r.val i j ≤ dist i j a b) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m, 0 <= j < n, 0 <= i' < m, 0 <= j' < n, |r[i][j] - r[i'][j']| <= |i-i'| + |j-j'|.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j i' j', i < m → j < n → i' < m → j' < n →
          |cellOf r.val i j - cellOf r.val i' j'| ≤ dist i j i' j' := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j i' j', i < m → j < n → i' < m → j' < n →
            |cellOf r.val i j - cellOf r.val i' j'| ≤ dist i j i' j') := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n with mat[i][j] = 1, let N(i,j) = { (a,b) : 0 <= a < m, 0 <= b < n, and (a = i+1 and b = j) or (a = i-1 and b = j) or (a = i and b = j+1) or (a = i and b = j-1) }. Then N(i,j) is nonempty and r[i][j] = 1 + min { r[a][b] : (a,b) in N(i,j) }.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n → cellOf mat.val i j = 1 →
          gridNeighbours m n i j ≠ [] ∧
            ∃ d, ((gridNeighbours m n i j).map (fun p => cellOf r.val p.1 p.2)).min? = some d ∧
              cellOf r.val i j = 1 + d := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → cellOf mat.val i j = 1 →
            gridNeighbours m n i j ≠ [] ∧
              ∃ d, ((gridNeighbours m n i j).map (fun p => cellOf r.val p.1 p.2)).min? = some d ∧
                cellOf r.val i j = 1 + d) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r and mat is invariant under left-right reflection, i.e. for every 0 <= i < m and 0 <= j < n, mat[i][j] = mat[i][n-1-j], then r is also invariant under left-right reflection: for every 0 <= i < m and 0 <= j < n, r[i][j] = r[i][n-1-j].
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_10 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      (∀ i j, i < m → j < n → cellOf mat.val i j = cellOf mat.val i (n - 1 - j)) →
        ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → cellOf r.val i j = cellOf r.val i (n - 1 - j) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), (∀ i j, i < m → j < n → cellOf mat.val i j = cellOf mat.val i (n - 1 - j)) →
          ∀ (r : OutMat), update_matrix mat = ok r →
            ∀ i j, i < m → j < n → cellOf r.val i j = cellOf r.val i (n - 1 - j)) := by
    sorry

  /-- For every mat satisfying the preconditions, update_matrix(mat) returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n (so mat is an m by n rectangular matrix), every entry mat[i][j] with 0 <= i < m and 0 <= j < n is either 0 or 1, and there is at least one zero cell, i.e. some (a,b) with 0 <= a < m, 0 <= b < n and mat[a][b] = 0. -/
  theorem spec_11 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0) :
      ∃ r, update_matrix mat = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0), ∃ r, update_matrix mat = ok r) := by
    sorry

  /-- Whenever update_matrix(mat1) returns a result r1 and update_matrix(mat2) returns a result r2, for every 0 <= i < m and 0 <= j < n, r2[i][j] <= r1[i][j].
    Preconditions: Let mat1 and mat2 be two m by n binary matrices satisfying: m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row has length n, every entry is 0 or 1, and each matrix has at least one zero cell. Assume every zero cell of mat1 is also a zero cell of mat2: for every 0 <= i < m and 0 <= j < n, mat1[i][j] = 0 implies mat2[i][j] = 0. -/
  theorem spec_12 (mat1 mat2 : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat1.val.length) (hn : n = (rowOf mat1.val 0).length)
      (hm2 : m = mat2.val.length) (hn2 : n = (rowOf mat2.val 0).length)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect1 : ∀ i, i < m → (rowOf mat1.val i).length = n)
      (hrect2 : ∀ i, i < m → (rowOf mat2.val i).length = n)
      (hentries1 : ∀ i j, i < m → j < n → cellOf mat1.val i j = 0 ∨ cellOf mat1.val i j = 1)
      (hentries2 : ∀ i j, i < m → j < n → cellOf mat2.val i j = 0 ∨ cellOf mat2.val i j = 1)
      (hzero1 : ∃ a b, a < m ∧ b < n ∧ cellOf mat1.val a b = 0)
      (hzero2 : ∃ a b, a < m ∧ b < n ∧ cellOf mat2.val a b = 0)
      (hsub : ∀ i j, i < m → j < n → cellOf mat1.val i j = 0 → cellOf mat2.val i j = 0) :
      ∀ (r1 r2 : OutMat), update_matrix mat1 = ok r1 → update_matrix mat2 = ok r2 →
        ∀ i j, i < m → j < n → cellOf r2.val i j ≤ cellOf r1.val i j := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat1.val.length) (hn : n = (rowOf mat1.val 0).length)
        (hm2 : m = mat2.val.length) (hn2 : n = (rowOf mat2.val 0).length)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect1 : ∀ i, i < m → (rowOf mat1.val i).length = n)
        (hrect2 : ∀ i, i < m → (rowOf mat2.val i).length = n)
        (hentries1 : ∀ i j, i < m → j < n → cellOf mat1.val i j = 0 ∨ cellOf mat1.val i j = 1)
        (hentries2 : ∀ i j, i < m → j < n → cellOf mat2.val i j = 0 ∨ cellOf mat2.val i j = 1)
        (hzero1 : ∃ a b, a < m ∧ b < n ∧ cellOf mat1.val a b = 0)
        (hzero2 : ∃ a b, a < m ∧ b < n ∧ cellOf mat2.val a b = 0)
        (hsub : ∀ i j, i < m → j < n → cellOf mat1.val i j = 0 → cellOf mat2.val i j = 0), ∀ (r1 r2 : OutMat), update_matrix mat1 = ok r1 → update_matrix mat2 = ok r2 →
          ∀ i j, i < m → j < n → cellOf r2.val i j ≤ cellOf r1.val i j) := by
    sorry

  /-- Whenever update_matrix(mat) returns a result r, for every 0 <= i < m and 0 <= j < n, r[i][j] = r[j][i].
    Preconditions: Let m = len(mat) and n = len(mat[0]). Assume m = n, m >= 1, n >= 1, m <= 10^4, n <= 10^4, m * n <= 10^4, every row of mat has length n, every entry is 0 or 1, there is at least one zero cell, and mat is symmetric under transpose: for every 0 <= i < m and 0 <= j < n, mat[i][j] = mat[j][i]. -/
  theorem spec_13 (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
      (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
      (hmn_eq : m = n)
      (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
      (hmn : m * n ≤ 10 ^ 4)
      (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
      (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
      (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0)
      (hsymm : ∀ i j, i < m → j < n → cellOf mat.val i j = cellOf mat.val j i) :
      ∀ (r : OutMat), update_matrix mat = ok r →
        ∀ i j, i < m → j < n → cellOf r.val i j = cellOf r.val j i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec I64)) (m n : Nat)
        (hm : m = mat.val.length) (hn : n = (rowOf mat.val 0).length)
        (hmn_eq : m = n)
        (hm1 : 1 ≤ m) (hn1 : 1 ≤ n) (hmle : m ≤ 10 ^ 4) (hnle : n ≤ 10 ^ 4)
        (hmn : m * n ≤ 10 ^ 4)
        (hrect : ∀ i, i < m → (rowOf mat.val i).length = n)
        (hentries : ∀ i j, i < m → j < n → cellOf mat.val i j = 0 ∨ cellOf mat.val i j = 1)
        (hzero : ∃ a b, a < m ∧ b < n ∧ cellOf mat.val a b = 0)
        (hsymm : ∀ i j, i < m → j < n → cellOf mat.val i j = cellOf mat.val j i), ∀ (r : OutMat), update_matrix mat = ok r →
          ∀ i j, i < m → j < n → cellOf r.val i j = cellOf r.val j i) := by
    sorry

  end AegisSpec.UpdateMatrix
