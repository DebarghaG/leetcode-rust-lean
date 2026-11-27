import Aegis.MatrixReshape.Code.Funs

/-!
# Specifications of `Aegis.MatrixReshape.matrix_reshape`

LeetCode problem `reshape-the-matrix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MatrixReshape

def rowMajor (rows : List (alloc.vec.Vec Std.I64)) : List Int :=
  (rows.map fun row => row.val.map fun x => x.val).flatten

/-- The function returns a result res such that: if m*n = R*C, then len(res) = R, len(res[i]) = C for every i with 0 <= i < R, and res[i][j] = mat[(i*C+j)/n][(i*C+j)%n] for every i,j with 0 <= i < R and 0 <= j < C; if m*n != R*C, then len(res) = m, len(res[i]) = n for every i with 0 <= i < m, and res[i][j] = mat[i][j] for every i,j with 0 <= i < m and 0 <= j < n.
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300. -/
theorem spec_1
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)

    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)

    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (if m * n = R * C then

        res.val.length = R ∧
        (∀ (i : Nat), i < R → (res.val[i]!).val.length = C) ∧
        (∀ (i j : Nat), i < R → j < C →
          ((res.val[i]!).val[j]!).val = ((mat.val[(i * C + j) / n]!).val[(i * C + j) % n]!).val)
      else

        res.val.length = m ∧
        (∀ (i : Nat), i < m → (res.val[i]!).val.length = n) ∧
        (∀ (i j : Nat), i < m → j < n →
          ((res.val[i]!).val[j]!).val = ((mat.val[i]!).val[j]!).val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)

    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)

    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (if m * n = R * C then

        res.val.length = R ∧
        (∀ (i : Nat), i < R → (res.val[i]!).val.length = C) ∧
        (∀ (i j : Nat), i < R → j < C →
          ((res.val[i]!).val[j]!).val = ((mat.val[(i * C + j) / n]!).val[(i * C + j) % n]!).val)
      else

        res.val.length = m ∧
        (∀ (i : Nat), i < m → (res.val[i]!).val.length = n) ∧
        (∀ (i j : Nat), i < m → j < n →
          ((res.val[i]!).val[j]!).val = ((mat.val[i]!).val[j]!).val))) := by
  sorry

/-- The function returns a result res (it does not fail, overflow, panic, or go out of bounds).
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300. -/
theorem spec_2
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res) := by
  sorry

/-- The function returns a result res with len(res) = R and, for every i with 0 <= i < R, len(res[i]) = C.
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300; also m*n = R*C. -/
theorem spec_3
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n = R * C) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      res.val.length = R ∧
      (∀ (i : Nat), i < R → (res.val[i]!).val.length = C) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n = R * C), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      res.val.length = R ∧
      (∀ (i : Nat), i < R → (res.val[i]!).val.length = C)) := by
  sorry

/-- The function returns a result res such that for every i,j with 0 <= i < R and 0 <= j < C, res[i][j] = mat[(i*C+j)/n][(i*C+j)%n].
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300; also m*n = R*C. -/
theorem spec_4
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n = R * C) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (∀ (i j : Nat), i < R → j < C →
        ((res.val[i]!).val[j]!).val = ((mat.val[(i * C + j) / n]!).val[(i * C + j) % n]!).val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n = R * C), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (∀ (i j : Nat), i < R → j < C →
        ((res.val[i]!).val[j]!).val = ((mat.val[(i * C + j) / n]!).val[(i * C + j) % n]!).val)) := by
  sorry

/-- The function returns a result res with len(res) = m and, for every i with 0 <= i < m, len(res[i]) = n.
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300; also m*n != R*C. -/
theorem spec_5
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n ≠ R * C) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      res.val.length = m ∧
      (∀ (i : Nat), i < m → (res.val[i]!).val.length = n) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n ≠ R * C), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      res.val.length = m ∧
      (∀ (i : Nat), i < m → (res.val[i]!).val.length = n)) := by
  sorry

/-- The function returns a result res such that for every i,j with 0 <= i < m and 0 <= j < n, res[i][j] = mat[i][j].
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300; also m*n != R*C. -/
theorem spec_6
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n ≠ R * C) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (∀ (i j : Nat), i < m → j < n →
        ((res.val[i]!).val[j]!).val = ((mat.val[i]!).val[j]!).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300)
    (htotal : m * n ≠ R * C), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧
      (∀ (i j : Nat), i < m → j < n →
        ((res.val[i]!).val[j]!).val = ((mat.val[i]!).val[j]!).val)) := by
  sorry

/-- The function returns a result res such that the sequence obtained by reading all entries of res in row-major order (rows top to bottom, and left to right within each row) is exactly the sequence obtained by reading all entries of mat in the same row-major order.
  Preconditions: Let m = len(mat). The input satisfies m >= 1 and m <= 100. Let n = len(mat[0]). Then n >= 1 and n <= 100; for every i with 0 <= i < m, len(mat[i]) = n; for every i,j with 0 <= i < m and 0 <= j < n, -1000 <= mat[i][j] <= 1000. Let R be the natural-number value of r and C the natural-number value of c; then 1 <= R <= 300 and 1 <= C <= 300. -/
theorem spec_7
    (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300) :
    ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧ rowMajor res.val = rowMajor mat.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (r c : Std.I64) (m n R C : Nat)
    (hm : mat.val.length = m)
    (hm_ge : 1 ≤ m) (hm_le : m ≤ 100)
    (hn_eq : (mat.val[0]!).val.length = n)
    (hn_ge : 1 ≤ n) (hn_le : n ≤ 100)
    (hrows : ∀ (i : Nat), i < m → (mat.val[i]!).val.length = n)
    (hentries : ∀ (i j : Nat), i < m → j < n →
      -1000 ≤ ((mat.val[i]!).val[j]!).val ∧ ((mat.val[i]!).val[j]!).val ≤ 1000)
    (hR : r.val = (R : Int)) (hR_ge : 1 ≤ R) (hR_le : R ≤ 300)
    (hC : c.val = (C : Int)) (hC_ge : 1 ≤ C) (hC_le : C ≤ 300), ∃ res : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.MatrixReshape.matrix_reshape mat r c = ok res ∧ rowMajor res.val = rowMajor mat.val) := by
  sorry

end AegisSpec.MatrixReshape
