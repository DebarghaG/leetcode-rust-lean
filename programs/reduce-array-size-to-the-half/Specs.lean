import Aegis.MinSetSize.Code.Funs

/-!
# Specifications of `Aegis.MinSetSize.min_set_size`

LeetCode problem `reduce-array-size-to-the-half`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinSetSize

  def vals (arr : Slice I64) : List ℤ := arr.val.map (fun x => x.val)

  def count (arr : Slice I64) (v : ℤ) : ℕ := (vals arr).count v

  def distinctVals (arr : Slice I64) : Finset ℤ := (vals arr).toFinset

  def half (arr : Slice I64) : ℤ := (arr.val.length : ℤ) / 2

  def countSum (arr : Slice I64) (S : Finset ℤ) : ℤ := S.sum (fun v => (count arr v : ℤ))

  def feasible (arr : Slice I64) (k : ℕ) : Prop :=
    ∃ S : Finset ℤ, S ⊆ distinctVals arr ∧ S.card = k ∧ half arr ≤ countSum arr S

  def maxCount (arr : Slice I64) : ℕ := (distinctVals arr).sup (count arr)

  def freqList (arr : Slice I64) : List ℕ := ((vals arr).dedup).map (count arr)

  def sortedFreqs (arr : Slice I64) : List ℕ :=
    List.insertionSort (fun a b : ℕ => b ≤ a) (freqList arr)

  def prefixCount (arr : Slice I64) (k : ℕ) : ℤ := (((sortedFreqs arr).take k).sum : ℤ)

  /-- The function returns a result r, and r is the least natural number k for which there exists a finite set S of integers such that S is a subset of D, |S| = k, and sum_{v in S} count(v) >= len(arr)/2. Here D is the set of distinct values occurring in arr, so v is in D exactly when count(v) > 0, and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. Since len(arr) is even, len(arr)/2 is the exact integer half of the array length.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_1 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∃ r : I64, Aegis.MinSetSize.min_set_size arr = ok r ∧ 0 ≤ r.val ∧
        IsLeast {k : ℕ | feasible arr k} r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∃ r : I64, Aegis.MinSetSize.min_set_size arr = ok r ∧ 0 ≤ r.val ∧
          IsLeast {k : ℕ | feasible arr k} r.val.toNat) := by
    sorry

  /-- For every arr satisfying the preconditions, the function returns a result r; it does not fail.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_2 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∃ r : I64, Aegis.MinSetSize.min_set_size arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∃ r : I64, Aegis.MinSetSize.min_set_size arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_3 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= |D|, where D is the set of distinct values occurring in arr.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_4 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        r.val ≤ ((distinctVals arr).card : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          r.val ≤ ((distinctVals arr).card : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(arr)/2.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_5 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → r.val ≤ half arr := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → r.val ≤ half arr) := by
    sorry

  /-- Whenever the function returns a result r, there exists a set S of integers such that S is a subset of D, |S| = r, and sum_{v in S} count(v) >= len(arr)/2, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_6 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        ∃ S : Finset ℤ, S ⊆ distinctVals arr ∧ (S.card : ℤ) = r.val ∧
          half arr ≤ countSum arr S := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          ∃ S : Finset ℤ, S ⊆ distinctVals arr ∧ (S.card : ℤ) = r.val ∧
            half arr ≤ countSum arr S) := by
    sorry

  /-- Whenever the function returns a result r, for every set S of integers such that S is a subset of D and |S| < r, we have sum_{v in S} count(v) < len(arr)/2, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_7 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        ∀ S : Finset ℤ, S ⊆ distinctVals arr → (S.card : ℤ) < r.val →
          countSum arr S < half arr := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          ∀ S : Finset ℤ, S ⊆ distinctVals arr → (S.card : ℤ) < r.val →
            countSum arr S < half arr) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists a value v in D with count(v) >= len(arr)/2, where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_8 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        (r.val = 1 ↔ ∃ v ∈ distinctVals arr, half arr ≤ (count arr v : ℤ)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          (r.val = 1 ↔ ∃ v ∈ distinctVals arr, half arr ≤ (count arr v : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r, r = len(arr)/2.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and for every i and j with 0 <= i < j < len(arr), arr[i] != arr[j]. -/
  theorem spec_9 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
      (hnodup : ∀ i j (hi : i < arr.val.length) (hj : j < arr.val.length), i < j →
        (arr.val[i]'hi).val ≠ (arr.val[j]'hj).val) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → r.val = half arr := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
        (hnodup : ∀ i j (hi : i < arr.val.length) (hj : j < arr.val.length), i < j →
          (arr.val[i]'hi).val ≠ (arr.val[j]'hj).val), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → r.val = half arr) := by
    sorry

  /-- Whenever the function returns a result r, let a, b, c be the three frequencies count(v) for the three values v in D. Then r = 1 if max(a,b,c) >= len(arr)/2, and r = 2 otherwise.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000, and the set D of distinct values occurring in arr has exactly three elements. -/
  theorem spec_10 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
      (hD3 : (distinctVals arr).card = 3) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        r.val = if half arr ≤ (maxCount arr : ℤ) then 1 else 2 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
        (hD3 : (distinctVals arr).card = 3), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          r.val = if half arr ≤ (maxCount arr : ℤ) then 1 else 2) := by
    sorry

  /-- Whenever the function returns a result r, let fmax = max_{v in D} count(v), where D is the set of distinct values occurring in arr and count(v) is the number of indices i with 0 <= i < len(arr) and arr[i] = v. Then r * fmax >= len(arr)/2.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_11 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        half arr ≤ r.val * (maxCount arr : ℤ) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          half arr ≤ r.val * (maxCount arr : ℤ)) := by
    sorry

  /-- If min_set_size arr returns a result r and min_set_size arr' returns a result r', then r = r'.
    Preconditions: arr and arr' are slices of 64-bit integers, each satisfying 2 <= len(arr) <= 100000, even length, and entries in the range 1..100000; moreover, for every integer v, the number of indices i with arr[i] = v equals the number of indices j with arr'[j] = v. -/
  theorem spec_12 (arr arr' : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
      (hlen2' : 2 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 100000)
      (heven' : arr'.val.length % 2 = 0)
      (hrange' : ∀ i (hi : i < arr'.val.length),
        1 ≤ (arr'.val[i]'hi).val ∧ (arr'.val[i]'hi).val ≤ 100000)
      (hcount : ∀ v : ℤ, count arr v = count arr' v) :
      ∀ r r' : I64, Aegis.MinSetSize.min_set_size arr = ok r →
        Aegis.MinSetSize.min_set_size arr' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr arr' : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000)
        (hlen2' : 2 ≤ arr'.val.length) (hlen_le' : arr'.val.length ≤ 100000)
        (heven' : arr'.val.length % 2 = 0)
        (hrange' : ∀ i (hi : i < arr'.val.length),
          1 ≤ (arr'.val[i]'hi).val ∧ (arr'.val[i]'hi).val ≤ 100000)
        (hcount : ∀ v : ℤ, count arr v = count arr' v), ∀ r r' : I64, Aegis.MinSetSize.min_set_size arr = ok r →
          Aegis.MinSetSize.min_set_size arr' = ok r' → r.val = r'.val) := by
    sorry

  /-- Let D be the set of distinct values occurring in arr, let count(v) be the number of indices i with 0 <= i < len(arr) and arr[i] = v, and let f_1 >= f_2 >= ... >= f_m be the frequencies count(v) for v in D sorted in nonincreasing order. Whenever the function returns a result r, r is the least k with 1 <= k <= m and sum_{i=1}^k f_i >= len(arr)/2.
    Preconditions: arr is a slice of 64-bit integers with 2 <= len(arr) <= 100000, len(arr) is even, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 100000. -/
  theorem spec_13 (arr : Slice I64)
      (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (heven : arr.val.length % 2 = 0)
      (hrange : ∀ i (hi : i < arr.val.length),
        1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000) :
      ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → 0 ≤ r.val ∧
        IsLeast {k : ℕ | 1 ≤ k ∧ k ≤ (sortedFreqs arr).length ∧ half arr ≤ prefixCount arr k}
          r.val.toNat := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr : Slice I64)
        (hlen2 : 2 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (heven : arr.val.length % 2 = 0)
        (hrange : ∀ i (hi : i < arr.val.length),
          1 ≤ (arr.val[i]'hi).val ∧ (arr.val[i]'hi).val ≤ 100000), ∀ r : I64, Aegis.MinSetSize.min_set_size arr = ok r → 0 ≤ r.val ∧
          IsLeast {k : ℕ | 1 ≤ k ∧ k ≤ (sortedFreqs arr).length ∧ half arr ≤ prefixCount arr k}
            r.val.toNat) := by
    sorry

  end AegisSpec.MinSetSize
