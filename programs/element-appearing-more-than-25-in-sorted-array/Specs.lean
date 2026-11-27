import Aegis.FindSpecialInteger.Code.Funs

/-!
# Specifications of `Aegis.FindSpecialInteger.find_special_integer`

LeetCode problem `element-appearing-more-than-25-in-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

  namespace AegisSpec.FindSpecialInteger

  def valueAt (arr : Slice Std.I64) (i : Nat) (h : i < arr.length) : Int :=
    (arr.val[i]'h).val

  def occAt (arr : Slice Std.I64) (i : Nat) (v : Int) : Prop :=
    ∃ h : i < arr.length, valueAt arr i h = v

  def occurs (arr : Slice Std.I64) (v : Int) : Prop :=
    ∃ i : Nat, occAt arr i v

  def count (arr : Slice Std.I64) (v : Int) : Nat :=
    arr.val.countP (fun x => x.val = v)

  /-- The function returns a result r, and 4 * count(r) > len(arr), where count(r) is the number of indices i with 0 <= i < len(arr) and arr[i] = r.
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_1 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        4 * count arr r.val > arr.length := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          4 * count arr r.val > arr.length) := by
    sorry

  /-- The function returns a result r; that is, it does not fail (no arithmetic overflow, out-of-bounds access, or panic).
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_2 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r) := by
    sorry

  /-- The function returns a result r, and there exists an index i with 0 <= i < len(arr) such that arr[i] = r.
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_3 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∃ (i : Nat) (h : i < arr.length), valueAt arr i h = r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∃ (i : Nat) (h : i < arr.length), valueAt arr i h = r.val) := by
    sorry

  /-- The function returns a result r, and arr[0] <= r <= arr[len(arr)-1].
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_4 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∃ (h0 : 0 < arr.length) (hn : arr.length - 1 < arr.length),
          valueAt arr 0 h0 ≤ r.val ∧ r.val ≤ valueAt arr (arr.length - 1) hn := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∃ (h0 : 0 < arr.length) (hn : arr.length - 1 < arr.length),
            valueAt arr 0 h0 ≤ r.val ∧ r.val ≤ valueAt arr (arr.length - 1) hn) := by
    sorry

  /-- The function returns a result r, and for every integer v with v != r that occurs in arr (i.e., there exists i with 0 <= i < len(arr) and arr[i] = v), we have 4 * count(v) <= len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_5 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∀ v : Int, v ≠ r.val → occurs arr v → 4 * count arr v ≤ arr.length := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∀ v : Int, v ≠ r.val → occurs arr v → 4 * count arr v ≤ arr.length) := by
    sorry

  /-- The function returns a result r, and there exist indices i and j with 0 <= i <= j < len(arr) such that: arr[k] = r for every k with i <= k <= j; either i = 0 or arr[i-1] != r; either j = len(arr)-1 or arr[j+1] != r; and 4 * (j - i + 1) > len(arr).
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_6 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∃ (i j : Nat) (hij : i ≤ j) (hj : j < arr.length),
          (∀ (k : Nat), i ≤ k → k ≤ j → occAt arr k r.val) ∧
          (i = 0 ∨ ¬ occAt arr (i - 1) r.val) ∧
          (j + 1 = arr.length ∨ ¬ occAt arr (j + 1) r.val) ∧
          4 * (j - i + 1) > arr.length := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∃ (i j : Nat) (hij : i ≤ j) (hj : j < arr.length),
            (∀ (k : Nat), i ≤ k → k ≤ j → occAt arr k r.val) ∧
            (i = 0 ∨ ¬ occAt arr (i - 1) r.val) ∧
            (j + 1 = arr.length ∨ ¬ occAt arr (j + 1) r.val) ∧
            4 * (j - i + 1) > arr.length) := by
    sorry

  /-- The function returns a result r, and count(r) >= 2, where count(r) is the number of indices i with 0 <= i < len(arr) and arr[i] = r.
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v; len(arr) >= 2. -/
  theorem spec_7 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length)
      (h_len_ge_two : 2 ≤ arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        2 ≤ count arr r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length)
        (h_len_ge_two : 2 ≤ arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          2 ≤ count arr r.val) := by
    sorry

  /-- The function returns a result r, and for every integer v that occurs in arr with v != r, count(v) < count(r), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_8 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∀ v : Int, v ≠ r.val → occurs arr v → count arr v < count arr r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∀ v : Int, v ≠ r.val → occurs arr v → count arr v < count arr r.val) := by
    sorry

  /-- The function returns a result r, and (using integer division) r = arr[len(arr) / 4] or r = arr[len(arr) / 2] or r = arr[3 * len(arr) / 4].
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_9 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        (occAt arr (arr.length / 4) r.val ∨ occAt arr (arr.length / 2) r.val ∨
          occAt arr (3 * arr.length / 4) r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          (occAt arr (arr.length / 4) r.val ∨ occAt arr (arr.length / 2) r.val ∨
            occAt arr (3 * arr.length / 4) r.val)) := by
    sorry

  /-- The function returns a result r, and there exists an index i with 0 <= i < len(arr) - len(arr) / 4 such that arr[i] = r and arr[i + len(arr) / 4] = r (using integer division).
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_10 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∃ i : Nat, i < arr.length - arr.length / 4 ∧
          occAt arr i r.val ∧ occAt arr (i + arr.length / 4) r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∃ i : Nat, i < arr.length - arr.length / 4 ∧
            occAt arr i r.val ∧ occAt arr (i + arr.length / 4) r.val) := by
    sorry

  /-- The function returns a result r, and for every index i with 0 <= i < len(arr) - len(arr) / 4, if arr[i] = arr[i + len(arr) / 4] then arr[i] = r (using integer division).
    Preconditions: len(arr) >= 1 and len(arr) <= 10000; for every i with 0 <= i < len(arr), 0 <= arr[i] <= 100000; for every i, j with 0 <= i < j < len(arr), arr[i] <= arr[j]; and there is exactly one integer v such that 4 * count(v) > len(arr), where count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. -/
  theorem spec_11 (arr : Slice Std.I64)
      (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
      (h_val : ∀ (i : Nat) (h : i < arr.length),
        0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
      (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
        i < j → valueAt arr i hi ≤ valueAt arr j hj)
      (h_unique : ∃! v : Int, 4 * count arr v > arr.length) :
      ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
        ∀ (i : Nat), i < arr.length - arr.length / 4 →
          (∃ v : Int, occAt arr i v ∧ occAt arr (i + arr.length / 4) v) →
          occAt arr i r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (h_len_ge : 1 ≤ arr.length) (h_len_le : arr.length ≤ 10000)
        (h_val : ∀ (i : Nat) (h : i < arr.length),
          0 ≤ valueAt arr i h ∧ valueAt arr i h ≤ 100000)
        (h_sorted : ∀ (i j : Nat) (hi : i < arr.length) (hj : j < arr.length),
          i < j → valueAt arr i hi ≤ valueAt arr j hj)
        (h_unique : ∃! v : Int, 4 * count arr v > arr.length), ∃ r : Std.I64, Aegis.FindSpecialInteger.find_special_integer arr = ok r ∧
          ∀ (i : Nat), i < arr.length - arr.length / 4 →
            (∃ v : Int, occAt arr i v ∧ occAt arr (i + arr.length / 4) v) →
            occAt arr i r.val) := by
    sorry

  end AegisSpec.FindSpecialInteger
