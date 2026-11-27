import Aegis.Construct2DArray.Code.Funs

/-!
# Specifications of `Aegis.Construct2DArray.construct2_d_array`

LeetCode problem `convert-1d-array-into-2d-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.Construct2DArray

  abbrev VecI64 : Type := Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64

  abbrev VecVecI64 : Type := Aeneas.Std.alloc.vec.Vec VecI64

  /-- Whenever construct2_d_array returns a result r, the following holds: if len(original) = m*n, then len(r) = m, for every i with 0 <= i < m we have len(r[i]) = n, and for every i with 0 <= i < m and every j with 0 <= j < n we have r[i][j] = original[i*n + j]; if len(original) != m*n, then len(r) = 0, i.e. r is the empty 2D array having no rows at all.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. -/
  theorem spec_1
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      ((original.val.length : Int) = m.val * n.val →
          (r.val.length : Int) = m.val ∧
          (∀ (i : Nat), (i : Int) < m.val → ∀ row : VecI64,
              r.val[i]? = some row → (row.val.length : Int) = n.val) ∧
          (∀ (i j : Nat), (i : Int) < m.val → (j : Int) < n.val →
              ∀ (row : VecI64) (x y : Aeneas.Std.I64),
                r.val[i]? = some row → row.val[j]? = some x →
                original.val[i * n.val.toNat + j]? = some y → x.val = y.val)) ∧
      ((original.val.length : Int) ≠ m.val * n.val → r.val.length = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), ((original.val.length : Int) = m.val * n.val →
            (r.val.length : Int) = m.val ∧
            (∀ (i : Nat), (i : Int) < m.val → ∀ row : VecI64,
                r.val[i]? = some row → (row.val.length : Int) = n.val) ∧
            (∀ (i j : Nat), (i : Int) < m.val → (j : Int) < n.val →
                ∀ (row : VecI64) (x y : Aeneas.Std.I64),
                  r.val[i]? = some row → row.val[j]? = some x →
                  original.val[i * n.val.toNat + j]? = some y → x.val = y.val)) ∧
        ((original.val.length : Int) ≠ m.val * n.val → r.val.length = 0)) := by
    sorry

  /-- For every input satisfying the preconditions, construct2_d_array returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. -/
  theorem spec_2
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000) :
      ∃ r : VecVecI64,
        Aegis.Construct2DArray.construct2_d_array original m n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000), ∃ r : VecVecI64,
          Aegis.Construct2DArray.construct2_d_array original m n = ok r) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, len(r) = m.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. Additionally, len(original) = m*n. -/
  theorem spec_3
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (hlen : (original.val.length : Int) = m.val * n.val)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      (r.val.length : Int) = m.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (hlen : (original.val.length : Int) = m.val * n.val)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), (r.val.length : Int) = m.val) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, for every i with 0 <= i < m, the row r[i] exists and len(r[i]) = n.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. Additionally, len(original) = m*n. -/
  theorem spec_4
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (hlen : (original.val.length : Int) = m.val * n.val)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      ∀ (i : Nat), (i : Int) < m.val →
        ∃ row : VecI64, r.val[i]? = some row ∧ (row.val.length : Int) = n.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (hlen : (original.val.length : Int) = m.val * n.val)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), ∀ (i : Nat), (i : Int) < m.val →
          ∃ row : VecI64, r.val[i]? = some row ∧ (row.val.length : Int) = n.val) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, for every i with 0 <= i < m and every j with 0 <= j < n, the entry r[i][j] exists and equals original[i*n + j].
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. Additionally, len(original) = m*n. -/
  theorem spec_5
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (hlen : (original.val.length : Int) = m.val * n.val)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      ∀ (i j : Nat), (i : Int) < m.val → (j : Int) < n.val →
        ∀ (row : VecI64) (x y : Aeneas.Std.I64),
          r.val[i]? = some row → row.val[j]? = some x →
          original.val[i * n.val.toNat + j]? = some y → x.val = y.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (hlen : (original.val.length : Int) = m.val * n.val)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), ∀ (i j : Nat), (i : Int) < m.val → (j : Int) < n.val →
          ∀ (row : VecI64) (x y : Aeneas.Std.I64),
            r.val[i]? = some row → row.val[j]? = some x →
            original.val[i * n.val.toNat + j]? = some y → x.val = y.val) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, len(r) = 0; thus r has no rows and no entries.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. Additionally, len(original) != m*n. -/
  theorem spec_6
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (hlen : (original.val.length : Int) ≠ m.val * n.val)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      r.val.length = 0 ∧ r.val = [] := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (hlen : (original.val.length : Int) ≠ m.val * n.val)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), r.val.length = 0 ∧ r.val = []) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, len(r) = 0 if and only if len(original) != m*n.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. -/
  theorem spec_7
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      (r.val.length = 0 ↔ (original.val.length : Int) ≠ m.val * n.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), (r.val.length = 0 ↔ (original.val.length : Int) ≠ m.val * n.val)) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, the sum of the lengths of all rows of r is exactly len(original).
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. Additionally, len(original) = m*n. -/
  theorem spec_8
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (hlen : (original.val.length : Int) = m.val * n.val)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      (r.val.map (fun row => row.val.length)).sum = original.val.length := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (hlen : (original.val.length : Int) = m.val * n.val)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), (r.val.map (fun row => row.val.length)).sum = original.val.length) := by
    sorry

  /-- Whenever construct2_d_array returns a result r, every entry of r lies between 1 and 100000 inclusive: for every i with 0 <= i < len(r) and every j with 0 <= j < len(r[i]), 1 <= r[i][j] <= 100000.
    Preconditions: Let L = len(original). 1 <= L <= 50000; for every i with 0 <= i < L, 1 <= original[i] <= 100000; 1 <= m <= 40000; 1 <= n <= 40000. m and n are interpreted as mathematical integers, and all indices are 0-based. -/
  theorem spec_9
      (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
      (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
      (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
      (r : VecVecI64)
      (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r) :
      ∀ (i : Nat), i < r.val.length → ∀ row : VecI64, r.val[i]? = some row →
        ∀ (j : Nat), j < row.val.length → ∀ x : Aeneas.Std.I64,
          row.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ 100000 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (original : Aeneas.Std.Slice Aeneas.Std.I64) (m n : Aeneas.Std.I64)
        (hL_lo : 1 ≤ original.val.length) (hL_hi : original.val.length ≤ 50000)
        (h_orig : ∀ x ∈ original.val, 1 ≤ x.val ∧ x.val ≤ 100000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 40000)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 40000)
        (r : VecVecI64)
        (hres : Aegis.Construct2DArray.construct2_d_array original m n = ok r), ∀ (i : Nat), i < r.val.length → ∀ row : VecI64, r.val[i]? = some row →
          ∀ (j : Nat), j < row.val.length → ∀ x : Aeneas.Std.I64,
            row.val[j]? = some x → 1 ≤ x.val ∧ x.val ≤ 100000) := by
    sorry

  end AegisSpec.Construct2DArray
