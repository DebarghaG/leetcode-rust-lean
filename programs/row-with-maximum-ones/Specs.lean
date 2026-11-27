import Aegis.RowAndMaximumOnes.Code.Funs

/-!
# Specifications of `Aegis.RowAndMaximumOnes.row_and_maximum_ones`

LeetCode problem `row-with-maximum-ones`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RowAndMaximumOnes

  namespace AegisSpec.RowAndMaximumOnes

  def rowLen (mat : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    ((mat.val[i]?).map (fun row => row.val.length)).getD 0

  def ones (mat : Slice (alloc.vec.Vec Std.I64)) (i : ℕ) : ℕ :=
    ((mat.val[i]?).map (fun row => (row.val.filter (fun x => x.val = 1)).length)).getD 0

  def entry (mat : Slice (alloc.vec.Vec Std.I64)) (i j : ℕ) : ℤ :=
    ((mat.val[i]?).bind (fun row => (row.val[j]?).map (fun x => x.val))).getD 0

  def out (r : alloc.vec.Vec Std.I64) (k : ℕ) : ℤ :=
    ((r.val[k]?).map (fun x => x.val)).getD 0

  def outIdx (r : alloc.vec.Vec Std.I64) : ℤ := out r 0

  def outCount (r : alloc.vec.Vec Std.I64) : ℤ := out r 1

  def IsValidInputWith (mat : Slice (alloc.vec.Vec Std.I64)) (n : ℕ) : Prop :=
    1 ≤ mat.length ∧ mat.length ≤ 100 ∧ 1 ≤ n ∧ n ≤ 100 ∧
    (∀ i, i < mat.length → rowLen mat i = n) ∧
    (∀ i j, i < mat.length → j < n → entry mat i j = 0 ∨ entry mat i j = 1)

  def IsValidInput (mat : Slice (alloc.vec.Vec Std.I64)) : Prop :=
    ∃ n, IsValidInputWith mat n

  def IsFirstOneEntry (mat : Slice (alloc.vec.Vec Std.I64)) (k : ℕ) : Prop :=
    k < mat.length ∧ entry mat k 0 = 1 ∧ ∀ i, i < k → entry mat i 0 ≠ 1

  def IsFullOneRow (mat : Slice (alloc.vec.Vec Std.I64)) (n k : ℕ) : Prop :=
    k < mat.length ∧ ∀ j, j < n → entry mat k j = 1

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r, it holds that len(r) = 2, 0 <= r[0] < m, r[1] = ones(r[0]), for every i with 0 <= i < m we have ones(i) <= r[1], and for every i with 0 <= i < r[0] we have ones(i) < r[1].
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_1 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r →
        r.val.length = 2 ∧
        0 ≤ outIdx r ∧ outIdx r < (mat.length : ℤ) ∧
        outCount r = (ones mat (outIdx r).toNat : ℤ) ∧
        (∀ i, i < mat.length → (ones mat i : ℤ) ≤ outCount r) ∧
        (∀ i, i < (outIdx r).toNat → (ones mat i : ℤ) < outCount r) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r →
          r.val.length = 2 ∧
          0 ≤ outIdx r ∧ outIdx r < (mat.length : ℤ) ∧
          outCount r = (ones mat (outIdx r).toNat : ℤ) ∧
          (∀ i, i < mat.length → (ones mat i : ℤ) ≤ outCount r) ∧
          (∀ i, i < (outIdx r).toNat → (ones mat i : ℤ) < outCount r)) := by
    sorry

  /-- Under these preconditions, the function returns a result r and does not fail, panic, overflow, or go out of bounds.
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_2 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∃ r, row_and_maximum_ones mat = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∃ r, row_and_maximum_ones mat = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2.
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_3 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, we have 0 <= r[0] < len(mat).
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_4 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        0 ≤ outIdx r ∧ outIdx r < (mat.length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          0 ≤ outIdx r ∧ outIdx r < (mat.length : ℤ)) := by
    sorry

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r with len(r) = 2 and 0 <= r[0] < len(mat), we have r[1] = ones(r[0]).
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_5 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
        outCount r = (ones mat (outIdx r).toNat : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
          outCount r = (ones mat (outIdx r).toNat : ℤ)) := by
    sorry

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r with len(r) = 2, for every row index i with 0 <= i < len(mat) we have ones(i) <= r[1].
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_6 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        ∀ i, i < mat.length → (ones mat i : ℤ) ≤ outCount r := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          ∀ i, i < mat.length → (ones mat i : ℤ) ≤ outCount r) := by
    sorry

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r with len(r) = 2 and 0 <= r[0] < len(mat), for every i with 0 <= i < r[0] we have ones(i) < r[1].
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_7 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
        ∀ i, i < (outIdx r).toNat → (ones mat i : ℤ) < outCount r := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
          ∀ i, i < (outIdx r).toNat → (ones mat i : ℤ) < outCount r) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and 0 <= r[0] < len(mat), we have 0 <= r[1] <= len(mat[r[0]]).
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_8 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
        0 ≤ outCount r ∧ outCount r ≤ (rowLen mat (outIdx r).toNat : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
          0 ≤ outCount r ∧ outCount r ≤ (rowLen mat (outIdx r).toNat : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, if mat[i][j] = 0 for every 0 <= i < len(mat) and 0 <= j < len(mat[i]), then len(r) = 2, r[0] = 0, and r[1] = 0.
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_9 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r →
        (∀ i j, i < mat.length → j < rowLen mat i → entry mat i j = 0) →
        r.val.length = 2 ∧ outIdx r = 0 ∧ outCount r = 0 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r →
          (∀ i j, i < mat.length → j < rowLen mat i → entry mat i j = 0) →
          r.val.length = 2 ∧ outIdx r = 0 ∧ outCount r = 0) := by
    sorry

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r, if ones(i) = ones(0) for every 0 <= i < len(mat), then len(r) = 2, r[0] = 0, and r[1] = ones(0).
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_10 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r →
        (∀ i, i < mat.length → ones mat i = ones mat 0) →
        r.val.length = 2 ∧ outIdx r = 0 ∧ outCount r = (ones mat 0 : ℤ) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r →
          (∀ i, i < mat.length → ones mat i = ones mat 0) →
          r.val.length = 2 ∧ outIdx r = 0 ∧ outCount r = (ones mat 0 : ℤ)) := by
    sorry

  /-- Define ones(i) for 0 <= i < m as the number of indices j with 0 <= j < len(mat[i]) and mat[i][j] = 1. Whenever the function returns a result r, if n = 1, then len(r) = 2, r[1] = 1 if there exists an index i with 0 <= i < len(mat) and mat[i][0] = 1, and r[1] = 0 if no such index exists; moreover, r[0] is the smallest index i with 0 <= i < len(mat) and mat[i][0] = 1 if such an i exists, and r[0] = 0 otherwise.
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_11 (mat : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : IsValidInputWith mat n) (hn : n = 1) :
      ∀ r, row_and_maximum_ones mat = ok r →
        r.val.length = 2 ∧
        ((∃ k, IsFirstOneEntry mat k) →
          outCount r = 1 ∧ ∀ k, IsFirstOneEntry mat k → outIdx r = (k : ℤ)) ∧
        ((¬ ∃ k, IsFirstOneEntry mat k) → outCount r = 0 ∧ outIdx r = 0) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : IsValidInputWith mat n) (hn : n = 1), ∀ r, row_and_maximum_ones mat = ok r →
          r.val.length = 2 ∧
          ((∃ k, IsFirstOneEntry mat k) →
            outCount r = 1 ∧ ∀ k, IsFirstOneEntry mat k → outIdx r = (k : ℤ)) ∧
          ((¬ ∃ k, IsFirstOneEntry mat k) → outCount r = 0 ∧ outIdx r = 0)) := by
    sorry

  /-- Whenever the function returns a result r, if there exists an index k with 0 <= k < len(mat) such that mat[k][j] = 1 for every 0 <= j < n, then len(r) = 2, r[1] = n, and r[0] is the smallest such index k.
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_12 (mat : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
      (hvalid : IsValidInputWith mat n) :
      ∀ r, row_and_maximum_ones mat = ok r →
        (∃ k, IsFullOneRow mat n k) →
        r.val.length = 2 ∧ outCount r = (n : ℤ) ∧
        ∃ k, IsFullOneRow mat n k ∧ outIdx r = (k : ℤ) ∧
          ∀ k', IsFullOneRow mat n k' → k ≤ k' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (n : ℕ)
        (hvalid : IsValidInputWith mat n), ∀ r, row_and_maximum_ones mat = ok r →
          (∃ k, IsFullOneRow mat n k) →
          r.val.length = 2 ∧ outCount r = (n : ℤ) ∧
          ∃ k, IsFullOneRow mat n k ∧ outIdx r = (k : ℤ) ∧
            ∀ k', IsFullOneRow mat n k' → k ≤ k') := by
    sorry

  /-- If the function returns r on mat and s on mat2, then r = s.
    Preconditions: For each of two valid inputs mat and mat2, let their row counts be defined by ones(i) and ones2(i). We require len(mat) = len(mat2), 1 <= len(mat) <= 100, and for all valid row indices i, ones(i) = ones2(i). -/
  theorem spec_13 (mat mat2 : Slice (alloc.vec.Vec Std.I64))
      (hvalid : IsValidInput mat) (hvalid2 : IsValidInput mat2)
      (hlen : mat.length = mat2.length)
      (hones : ∀ i, i < mat.length → ones mat i = ones mat2 i) :
      ∀ r s, row_and_maximum_ones mat = ok r → row_and_maximum_ones mat2 = ok s → r = s := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (mat mat2 : Slice (alloc.vec.Vec Std.I64))
        (hvalid : IsValidInput mat) (hvalid2 : IsValidInput mat2)
        (hlen : mat.length = mat2.length)
        (hones : ∀ i, i < mat.length → ones mat i = ones mat2 i), ∀ r s, row_and_maximum_ones mat = ok r → row_and_maximum_ones mat2 = ok s → r = s) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2 and 0 <= r[0] < len(mat), r[1] = 0 if and only if mat[i][j] = 0 for every 0 <= i < len(mat) and 0 <= j < len(mat[i]).
    Preconditions: Let m = len(mat). We require 1 <= m <= 100 and that there is an integer n with 1 <= n <= 100 such that len(mat[i]) = n for every 0 <= i < m and mat[i][j] is either 0 or 1 for every 0 <= i < m and 0 <= j < n. -/
  theorem spec_14 (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat) :
      ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
        0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
        (outCount r = 0 ↔
          ∀ i j, i < mat.length → j < rowLen mat i → entry mat i j = 0) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (mat : Slice (alloc.vec.Vec Std.I64)) (hvalid : IsValidInput mat), ∀ r, row_and_maximum_ones mat = ok r → r.val.length = 2 →
          0 ≤ outIdx r → outIdx r < (mat.length : ℤ) →
          (outCount r = 0 ↔
            ∀ i j, i < mat.length → j < rowLen mat i → entry mat i j = 0)) := by
    sorry

  end AegisSpec.RowAndMaximumOnes
