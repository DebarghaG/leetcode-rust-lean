import Aegis.CountArrays.Code.Funs

/-!
# Specifications of `Aegis.CountArrays.count_arrays`

LeetCode problem `find-the-number-of-copy-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.CountArrays

  namespace AegisSpec.CountArrays

  def origAt (original : Slice Std.I64) (i : Nat) : ℤ :=
    ((original.val[i]?).map IScalar.val).getD 0

  def boundVals (bounds : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : List ℤ :=
    ((bounds.val[i]?).map (fun v => v.val.map IScalar.val)).getD []

  def boundLo (bounds : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ :=
    (boundVals bounds i).getD 0 0

  def boundHi (bounds : Slice (alloc.vec.Vec Std.I64)) (i : Nat) : ℤ :=
    (boundVals bounds i).getD 1 0

  def Lval (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (i : Nat) : ℤ :=
    boundLo bounds i - origAt original i

  def Uval (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (i : Nat) : ℤ :=
    boundHi bounds i - origAt original i

  def Lmax (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (List.max? ((List.range original.val.length).map (Lval original bounds))).getD 0

  def Umin (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64)) : ℤ :=
    (List.min? ((List.range original.val.length).map (Uval original bounds))).getD 0

  def IsValidCopy (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (copy : List ℤ) : Prop :=
    copy.length = original.val.length ∧
      (∀ i, i < original.val.length →
        boundLo bounds i ≤ copy.getD i 0 ∧ copy.getD i 0 ≤ boundHi bounds i) ∧
      (∀ i, 1 ≤ i → i < original.val.length →
        copy.getD i 0 - copy.getD (i - 1) 0
          = origAt original i - origAt original (i - 1))

  def copyMin (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    (List.range original.val.length).map (fun i => origAt original i + Lmax original bounds)

  def copyMax (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64)) : List ℤ :=
    (List.range original.val.length).map (fun i => origAt original i + Umin original bounds)

  /-- Whenever the function returns a result r, define L_i = bounds[i][0] - original[i] and U_i = bounds[i][1] - original[i] for 0 <= i < n, Lmax = max_{0 <= i < n} L_i, and Umin = min_{0 <= i < n} U_i. Then r = max(0, Umin - Lmax + 1). Equivalently, r is the number of integers c satisfying L_i <= c <= U_i for every i, which is the number of length-n integer arrays copy satisfying both (1) bounds[i][0] <= copy[i] <= bounds[i][1] for every i, and (2) copy[i] - copy[i-1] = original[i] - original[i-1] for every i with 1 <= i < n.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_1
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      r.val = max 0 (Umin original bounds - Lmax original bounds + 1) ∧

        Nat.card { c : ℤ // ∀ i, i < original.val.length →
            Lval original bounds i ≤ c ∧ c ≤ Uval original bounds i } = r.val.toNat ∧

        Nat.card { copy : List ℤ // IsValidCopy original bounds copy } = r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), r.val = max 0 (Umin original bounds - Lmax original bounds + 1) ∧

          Nat.card { c : ℤ // ∀ i, i < original.val.length →
              Lval original bounds i ≤ c ∧ c ≤ Uval original bounds i } = r.val.toNat ∧

          Nat.card { copy : List ℤ // IsValidCopy original bounds copy } = r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_2
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, r <= bounds[i][1] - bounds[i][0] + 1.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_3
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      ∀ i, i < original.val.length →
        r.val ≤ boundHi bounds i - boundLo bounds i + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), ∀ i, i < original.val.length →
          r.val ≤ boundHi bounds i - boundLo bounds i + 1) := by
    sorry

  /-- Whenever the function returns a result r, define L_i = bounds[i][0] - original[i], U_i = bounds[i][1] - original[i], Lmax = max_{0 <= i < n} L_i, and Umin = min_{0 <= i < n} U_i. Then r = 0 if and only if Umin < Lmax.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_4
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      r.val = 0 ↔ Umin original bounds < Lmax original bounds := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), r.val = 0 ↔ Umin original bounds < Lmax original bounds) := by
    sorry

  /-- Whenever the function returns a result r, with Lmax = max_{0 <= i < n} (bounds[i][0] - original[i]) and Umin = min_{0 <= i < n} (bounds[i][1] - original[i]), r = 1 if and only if Umin = Lmax.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_5
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      r.val = 1 ↔ Umin original bounds = Lmax original bounds := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), r.val = 1 ↔ Umin original bounds = Lmax original bounds) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, let Lmax = max_{0 <= i < n} (bounds[i][0] - original[i]). Then the array copy_min defined by copy_min[i] = original[i] + Lmax is a valid copy: it satisfies bounds[i][0] <= copy_min[i] <= bounds[i][1] for every i and copy_min[i] - copy_min[i-1] = original[i] - original[i-1] for every i with 1 <= i < n. Moreover, for every valid copy array copy and every i with 0 <= i < n, copy_min[i] <= copy[i].
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_6
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_pos : 0 < r.val) :
      IsValidCopy original bounds (copyMin original bounds) ∧
        ∀ copy : List ℤ, IsValidCopy original bounds copy →
          ∀ i, i < original.val.length →
            (copyMin original bounds).getD i 0 ≤ copy.getD i 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_pos : 0 < r.val), IsValidCopy original bounds (copyMin original bounds) ∧
          ∀ copy : List ℤ, IsValidCopy original bounds copy →
            ∀ i, i < original.val.length →
              (copyMin original bounds).getD i 0 ≤ copy.getD i 0) := by
    sorry

  /-- Whenever the function returns a result r with r = 0, there is no length-n integer array copy satisfying both bounds[i][0] <= copy[i] <= bounds[i][1] for every i and copy[i] - copy[i-1] = original[i] - original[i-1] for every i with 1 <= i < n.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_7
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_zero : r.val = 0) :
      ¬ ∃ copy : List ℤ, IsValidCopy original bounds copy := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_zero : r.val = 0), ¬ ∃ copy : List ℤ, IsValidCopy original bounds copy) := by
    sorry

  /-- Whenever count_arrays(original, bounds) returns a result r and count_arrays(original, bounds') returns a result r', we have r <= r'.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. Let bounds' be another slice of vectors with len(bounds') = n and for every i with 0 <= i < n: len(bounds'[i]) = 2, 1 <= bounds'[i][0] <= bounds[i][0], and bounds[i][1] <= bounds'[i][1] <= 1000000000. -/
  theorem spec_8
      (original : Slice Std.I64) (bounds bounds' : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (h_bounds'_len : bounds'.val.length = original.val.length)
      (h_shape' : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds'.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ boundLo bounds i ∧ boundHi bounds i ≤ hi.val ∧
              hi.val ≤ 1000000000)
      (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
      (hr' : count_arrays original bounds' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds bounds' : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (h_bounds'_len : bounds'.val.length = original.val.length)
        (h_shape' : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds'.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ boundLo bounds i ∧ boundHi bounds i ≤ hi.val ∧
                hi.val ≤ 1000000000)
        (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
        (hr' : count_arrays original bounds' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- Whenever count_arrays(original, bounds) returns a result r and count_arrays(original', bounds) returns a result r', we have r = r'.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. Let d be an integer and let original' be a slice of i64 with len(original') = n such that original'[i] = original[i] + d for every i with 0 <= i < n, and 1 <= original'[i] <= 1000000000 for every i. -/
  theorem spec_9
      (original original' : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (d : ℤ) (h_original'_len : original'.val.length = original.val.length)
      (h_original' : ∀ i, i < original.val.length →
        ∃ o o' : Std.I64, original.val[i]? = some o ∧ original'.val[i]? = some o' ∧
          o'.val = o.val + d ∧ 1 ≤ o'.val ∧ o'.val ≤ 1000000000)
      (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
      (hr' : count_arrays original' bounds = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (original original' : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (d : ℤ) (h_original'_len : original'.val.length = original.val.length)
        (h_original' : ∀ i, i < original.val.length →
          ∃ o o' : Std.I64, original.val[i]? = some o ∧ original'.val[i]? = some o' ∧
            o'.val = o.val + d ∧ 1 ≤ o'.val ∧ o'.val ≤ 1000000000)
        (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
        (hr' : count_arrays original' bounds = ok r'), r.val = r'.val) := by
    sorry

  /-- Whenever count_arrays(original, bounds) returns a result r and count_arrays(original', bounds') returns a result r', we have r = r'.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. Let d be an integer, and let original' and bounds' be slices with len(original') = n, len(bounds') = n, and for every i with 0 <= i < n: original'[i] = original[i] + d, len(bounds'[i]) = 2, bounds'[i][0] = bounds[i][0] + d, and bounds'[i][1] = bounds[i][1] + d. Assume (original', bounds') also satisfies the same shape and value-range preconditions as (original, bounds), in particular all new values are between 1 and 1000000000. -/
  theorem spec_10
      (original original' : Slice Std.I64) (bounds bounds' : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (d : ℤ)
      (h_original'_len : original'.val.length = original.val.length)
      (h_original' : ∀ i, i < original.val.length →
        ∃ o o' : Std.I64, original.val[i]? = some o ∧ original'.val[i]? = some o' ∧
          o'.val = o.val + d ∧ 1 ≤ o'.val ∧ o'.val ≤ 1000000000)

      (h_bounds' : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            ∃ (v' : alloc.vec.Vec Std.I64) (lo' hi' : Std.I64),
              bounds'.val[i]? = some v' ∧ v'.val = [lo', hi'] ∧
                lo'.val = lo.val + d ∧ hi'.val = hi.val + d)

      (h_bounds'_len : bounds'.val.length = original'.val.length)
      (h_shape' : ∀ i, i < original'.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds'.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
      (hr' : count_arrays original' bounds' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (original original' : Slice Std.I64) (bounds bounds' : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (d : ℤ)
        (h_original'_len : original'.val.length = original.val.length)
        (h_original' : ∀ i, i < original.val.length →
          ∃ o o' : Std.I64, original.val[i]? = some o ∧ original'.val[i]? = some o' ∧
            o'.val = o.val + d ∧ 1 ≤ o'.val ∧ o'.val ≤ 1000000000)

        (h_bounds' : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              ∃ (v' : alloc.vec.Vec Std.I64) (lo' hi' : Std.I64),
                bounds'.val[i]? = some v' ∧ v'.val = [lo', hi'] ∧
                  lo'.val = lo.val + d ∧ hi'.val = hi.val + d)

        (h_bounds'_len : bounds'.val.length = original'.val.length)
        (h_shape' : ∀ i, i < original'.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds'.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (r r' : Std.I64) (hr : count_arrays original bounds = ok r)
        (hr' : count_arrays original' bounds' = ok r'), r.val = r'.val) := by
    sorry

  /-- The function returns a result r; it does not fail by arithmetic overflow, out-of-bounds indexing, or panic.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_11
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000) :
      ∃ r : Std.I64, count_arrays original bounds = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000), ∃ r : Std.I64, count_arrays original bounds = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if bounds[i][0] <= original[i] <= bounds[i][1] for every i with 0 <= i < n, then r >= 1.
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_12
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (h_in : ∀ i, i < original.val.length →
        boundLo bounds i ≤ origAt original i ∧ origAt original i ≤ boundHi bounds i)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (h_in : ∀ i, i < original.val.length →
          boundLo bounds i ≤ origAt original i ∧ origAt original i ≤ boundHi bounds i)
        (r : Std.I64) (hr : count_arrays original bounds = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, let Umin = min_{0 <= i < n} (bounds[i][1] - original[i]). Then the array copy_max defined by copy_max[i] = original[i] + Umin for 0 <= i < n is a valid copy: it satisfies bounds[i][0] <= copy_max[i] <= bounds[i][1] for every i and copy_max[i] - copy_max[i-1] = original[i] - original[i-1] for every i with 1 <= i < n. Moreover, for every valid copy array copy and every i with 0 <= i < n, copy[i] <= copy_max[i].
    Preconditions: Let n = len(original). The input satisfies 2 <= n <= 100000, len(bounds) = n, and for every i with 0 <= i < n: len(bounds[i]) = 2, 1 <= original[i] <= 1000000000, and 1 <= bounds[i][0] <= bounds[i][1] <= 1000000000. -/
  theorem spec_13
      (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
      (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
      (h_bounds_len : bounds.val.length = original.val.length)
      (h_shape : ∀ i, i < original.val.length →
        ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
          bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
            1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
      (h_orig : ∀ i, i < original.val.length →
        ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
      (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_pos : 0 < r.val) :
      IsValidCopy original bounds (copyMax original bounds) ∧
        ∀ copy : List ℤ, IsValidCopy original bounds copy →
          ∀ i, i < original.val.length →
            copy.getD i 0 ≤ (copyMax original bounds).getD i 0 := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (original : Slice Std.I64) (bounds : Slice (alloc.vec.Vec Std.I64))
        (h_n_lo : 2 ≤ original.val.length) (h_n_hi : original.val.length ≤ 100000)
        (h_bounds_len : bounds.val.length = original.val.length)
        (h_shape : ∀ i, i < original.val.length →
          ∃ (v : alloc.vec.Vec Std.I64) (lo hi : Std.I64),
            bounds.val[i]? = some v ∧ v.val = [lo, hi] ∧
              1 ≤ lo.val ∧ lo.val ≤ hi.val ∧ hi.val ≤ 1000000000)
        (h_orig : ∀ i, i < original.val.length →
          ∃ o : Std.I64, original.val[i]? = some o ∧ 1 ≤ o.val ∧ o.val ≤ 1000000000)
        (r : Std.I64) (hr : count_arrays original bounds = ok r) (hr_pos : 0 < r.val), IsValidCopy original bounds (copyMax original bounds) ∧
          ∀ copy : List ℤ, IsValidCopy original bounds copy →
            ∀ i, i < original.val.length →
              copy.getD i 0 ≤ (copyMax original bounds).getD i 0) := by
    sorry

  end AegisSpec.CountArrays
