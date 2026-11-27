import Aegis.Multiply.Code.Funs

/-!
# Specifications of `Aegis.Multiply.multiply`

LeetCode problem `sparse-matrix-multiplication`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Multiply

def eltList (rows : List (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ :=
  match rows[i]? with
  | none => 0
  | some row => ((row.val[j]?).map (fun x => x.val)).getD 0

def elt (mat : Slice (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ := eltList mat.val i j

def eltRes (mat : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i j : Nat) : ℤ := eltList mat.val i j

def rowLenList (rows : List (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  ((rows[i]?).map (fun row => row.val.length)).getD 0

def rowLen (mat : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : Nat := rowLenList mat.val i

def rowLenRes (mat : alloc.vec.Vec (alloc.vec.Vec Std.I64)) (i : Nat) : Nat :=
  rowLenList mat.val i

def dot (mat1 mat2 : Slice (alloc.vec.Vec Std.I64)) (i j k : Nat) : ℤ :=
  ∑ t ∈ Finset.range k, elt mat1 i t * elt mat2 t j

def dotExcept (mat1 mat2 : Slice (alloc.vec.Vec Std.I64)) (i j k t : Nat) : ℤ :=
  ∑ s ∈ (Finset.range k).erase t, elt mat1 i s * elt mat2 s j

/-- The function returns a result r such that len(r) = m, for every i with 0 <= i < m we have len(r[i]) = n, and for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = sum_{t=0}^{k-1} mat1[i][t] * mat2[t][j], with the sum and products interpreted as mathematical integers.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_1 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r ∧
      r.val.length = mat1.val.length ∧
      (∀ i, i < mat1.val.length → rowLenRes r i = rowLen mat2 0) ∧
      (∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
        eltRes r i j = dot mat1 mat2 i j mat2.val.length) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r ∧
      r.val.length = mat1.val.length ∧
      (∀ i, i < mat1.val.length → rowLenRes r i = rowLen mat2 0) ∧
      (∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
        eltRes r i j = dot mat1 mat2 i j mat2.val.length)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(mat1).
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_2 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r → r.val.length = mat1.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r → r.val.length = mat1.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(mat1), len(r[i]) = len(mat2[0]).
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_3 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i, i < mat1.val.length → rowLenRes r i = rowLen mat2 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i, i < mat1.val.length → rowLenRes r i = rowLen mat2 0) := by
  sorry

/-- Whenever the function returns a result r, for every i,j with 0 <= i < m and 0 <= j < n, -10000*k <= r[i][j] <= 10000*k.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_4 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
          -(10000 * (mat2.val.length : ℤ)) ≤ eltRes r i j ∧
            eltRes r i j ≤ 10000 * (mat2.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
          -(10000 * (mat2.val.length : ℤ)) ≤ eltRes r i j ∧
            eltRes r i j ≤ 10000 * (mat2.val.length : ℤ)) := by
  sorry

/-- For every pair mat1, mat2 satisfying the preconditions, the function returns a result r; it does not fail with arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_5 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r ∧
      ∀ e : Error, Aegis.Multiply.multiply mat1 mat2 ≠ fail e := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∃ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r ∧
      ∀ e : Error, Aegis.Multiply.multiply mat1 mat2 ≠ fail e) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < m, if mat1[i][t] = 0 for every t with 0 <= t < k, then for every j with 0 <= j < n, r[i][j] = 0.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_6 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i, i < mat1.val.length →
          (∀ t, t < mat2.val.length → elt mat1 i t = 0) →
            ∀ j, j < rowLen mat2 0 → eltRes r i j = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i, i < mat1.val.length →
          (∀ t, t < mat2.val.length → elt mat1 i t = 0) →
            ∀ j, j < rowLen mat2 0 → eltRes r i j = 0) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < n, if mat2[t][j] = 0 for every t with 0 <= t < k, then for every i with 0 <= i < m, r[i][j] = 0.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_7 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ j, j < rowLen mat2 0 →
          (∀ t, t < mat2.val.length → elt mat2 t j = 0) →
            ∀ i, i < mat1.val.length → eltRes r i j = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ j, j < rowLen mat2 0 →
          (∀ t, t < mat2.val.length → elt mat2 t j = 0) →
            ∀ i, i < mat1.val.length → eltRes r i j = 0) := by
  sorry

/-- Whenever the function returns a result r, for every i,i' with 0 <= i < m and 0 <= i' < m, if mat1[i][t] = mat1[i'][t] for every t with 0 <= t < k, then for every j with 0 <= j < n, r[i][j] = r[i'][j].
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_8 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i i', i < mat1.val.length → i' < mat1.val.length →
          (∀ t, t < mat2.val.length → elt mat1 i t = elt mat1 i' t) →
            ∀ j, j < rowLen mat2 0 → eltRes r i j = eltRes r i' j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ i i', i < mat1.val.length → i' < mat1.val.length →
          (∀ t, t < mat2.val.length → elt mat1 i t = elt mat1 i' t) →
            ∀ j, j < rowLen mat2 0 → eltRes r i j = eltRes r i' j) := by
  sorry

/-- Whenever the function returns a result r, for every j,j' with 0 <= j < n and 0 <= j' < n, if mat2[t][j] = mat2[t][j'] for every t with 0 <= t < k, then for every i with 0 <= i < m, r[i][j] = r[i][j'].
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_9 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ j j', j < rowLen mat2 0 → j' < rowLen mat2 0 →
          (∀ t, t < mat2.val.length → elt mat2 t j = elt mat2 t j') →
            ∀ i, i < mat1.val.length → eltRes r i j = eltRes r i j' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ j j', j < rowLen mat2 0 → j' < rowLen mat2 0 →
          (∀ t, t < mat2.val.length → elt mat2 t j = elt mat2 t j') →
            ∀ i, i < mat1.val.length → eltRes r i j = eltRes r i j') := by
  sorry

/-- Whenever the function returns a result r, for every t with 0 <= t < k, if either (mat1[i][t] = 0 for every i with 0 <= i < m) or (mat2[t][j] = 0 for every j with 0 <= j < n), then for every i,j with 0 <= i < m and 0 <= j < n, r[i][j] = sum_{s=0, s != t}^{k-1} mat1[i][s] * mat2[s][j], with the sum and products interpreted as mathematical integers.
  Preconditions: Let m = len(mat1), k = len(mat2), and n = len(mat2[0]). Assume 1 <= m <= 100, 1 <= k <= 100, 1 <= n <= 100; for every i with 0 <= i < m, len(mat1[i]) = k; for every i with 0 <= i < k, len(mat2[i]) = n; for every i,t with 0 <= i < m and 0 <= t < k, -100 <= mat1[i][t] <= 100; for every t,j with 0 <= t < k and 0 <= j < n, -100 <= mat2[t][j] <= 100. -/
theorem spec_10 (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100) :
    ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ t, t < mat2.val.length →
          ((∀ i, i < mat1.val.length → elt mat1 i t = 0) ∨
            (∀ j, j < rowLen mat2 0 → elt mat2 t j = 0)) →
            ∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
              eltRes r i j = dotExcept mat1 mat2 i j mat2.val.length t := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (mat1 mat2 : Slice (alloc.vec.Vec Std.I64))
    (hm_lo : 1 ≤ mat1.val.length) (hm_hi : mat1.val.length ≤ 100)
    (hk_lo : 1 ≤ mat2.val.length) (hk_hi : mat2.val.length ≤ 100)
    (hn_lo : 1 ≤ rowLen mat2 0) (hn_hi : rowLen mat2 0 ≤ 100)
    (hmat1 : ∀ i, i < mat1.val.length → rowLen mat1 i = mat2.val.length)
    (hmat2 : ∀ i, i < mat2.val.length → rowLen mat2 i = rowLen mat2 0)
    (hbound1 : ∀ i t, i < mat1.val.length → t < mat2.val.length →
      -100 ≤ elt mat1 i t ∧ elt mat1 i t ≤ 100)
    (hbound2 : ∀ t j, t < mat2.val.length → j < rowLen mat2 0 →
      -100 ≤ elt mat2 t j ∧ elt mat2 t j ≤ 100), ∀ r : alloc.vec.Vec (alloc.vec.Vec Std.I64),
      Aegis.Multiply.multiply mat1 mat2 = ok r →
        ∀ t, t < mat2.val.length →
          ((∀ i, i < mat1.val.length → elt mat1 i t = 0) ∨
            (∀ j, j < rowLen mat2 0 → elt mat2 t j = 0)) →
            ∀ i j, i < mat1.val.length → j < rowLen mat2 0 →
              eltRes r i j = dotExcept mat1 mat2 i j mat2.val.length t) := by
  sorry

end AegisSpec.Multiply
