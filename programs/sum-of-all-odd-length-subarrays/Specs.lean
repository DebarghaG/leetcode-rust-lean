import Aegis.SumOddLengthSubarrays.Code.Funs

/-!
# Specifications of `Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays`

LeetCode problem `sum-of-all-odd-length-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SumOddLengthSubarrays

  def entry (arr : Slice Std.I64) (i : ℕ) : ℤ :=
    ((arr.val[i]?).map (fun (x : Std.I64) => x.val)).getD 0

  def segSum (arr : Slice Std.I64) (i j : ℕ) : ℤ :=
    ∑ k ∈ Finset.range (j + 1 - i), entry arr (i + k)

  def oddSum (arr : Slice Std.I64) : ℤ :=
    ∑ i ∈ Finset.range arr.length, ∑ j ∈ Finset.range arr.length,
      if i ≤ j ∧ (j - i) % 2 = 0 then segSum arr i j else 0

  def A (n : ℕ) : ℤ :=
    ∑ L ∈ Finset.Icc 1 n, if L % 2 = 1 then (L : ℤ) * ((n : ℤ) - (L : ℤ) + 1) else 0

  def coverPairs (n i : ℕ) : Finset (ℕ × ℕ) :=
    ((Finset.range n).product (Finset.range n)).filter
      (fun p : ℕ × ℕ => p.1 ≤ i ∧ i ≤ p.2 ∧ (p.2 - p.1) % 2 = 0)

  def coverCount (n i : ℕ) : ℤ := ((coverPairs n i).card : ℤ)

  def coeffS6 (n i : ℕ) : ℤ :=
    (((i / 2 : ℕ) : ℤ) + 1) * ((((n - 1 - i) / 2 : ℕ) : ℤ) + 1)
      + (((i + 1) / 2 : ℕ) : ℤ) * ((((n - 1 - i) + 1) / 2 : ℕ) : ℤ)

  /-- The function returns a result r and does not fail. Let n = len(arr). Then r is the sum, over every pair of indices (i, j) with 0 <= i <= j < n and j - i even, of the contiguous subarray sum arr[i] + arr[i+1] + ... + arr[j]. Equivalently, r is the sum of the sums of all nonempty contiguous subarrays of arr whose length is odd; each such subarray is counted exactly once.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_1 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r ∧ r.val = oddSum arr := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∃ r : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r ∧ r.val = oddSum arr) := by
    sorry

  /-- For every arr satisfying the preconditions, the call sum_odd_length_subarrays(arr) returns a result r; it does not panic, go out of bounds, or overflow.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_2 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∃ r : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= sum_{i=0}^{len(arr)-1} arr[i].
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_3 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        (∑ i ∈ Finset.range arr.length, entry arr i) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          (∑ i ∈ Finset.range arr.length, entry arr i) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(arr) and let A(n) = sum over odd L with 1 <= L <= n of L * (n - L + 1). Then r <= 1000 * A(n).
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_4 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        r.val ≤ 1000 * A arr.length := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          r.val ≤ 1000 * A arr.length) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(arr). For each i with 0 <= i < n, let c_i be the number of pairs (l, u) such that 0 <= l <= i <= u < n and u - l is even. Then r = sum_{i=0}^{n-1} arr[i] * c_i.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_5 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        r.val = ∑ i ∈ Finset.range arr.length, entry arr i * coverCount arr.length i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          r.val = ∑ i ∈ Finset.range arr.length, entry arr i * coverCount arr.length i) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(arr). Then r = sum_{i=0}^{n-1} arr[i] * ( (floor(i/2) + 1) * (floor((n-1-i)/2) + 1) + ceil(i/2) * ceil((n-1-i)/2) ).
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_6 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        r.val = ∑ i ∈ Finset.range arr.length, entry arr i * coeffS6 arr.length i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          r.val = ∑ i ∈ Finset.range arr.length, entry arr i * coeffS6 arr.length i) := by
    sorry

  /-- Whenever the function returns r for arr and s for rev, r = s.
    Preconditions: arr satisfies 1 <= len(arr) <= 100 and entries in [1, 1000]. Let n = len(arr), and let rev be the slice of length n with rev[i] = arr[n-1-i] for 0 <= i < n; rev also satisfies the same constraints. -/
  theorem spec_7 (arr rev : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
      (hrev_val : rev.val = arr.val.reverse)
      (hrev_lo : 1 ≤ rev.length) (hrev_hi : rev.length ≤ 100)
      (hrev_entries : ∀ i, i < rev.length → 1 ≤ entry rev i ∧ entry rev i ≤ 1000) :
      ∀ r s : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays rev = ok s → r = s := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr rev : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
        (hrev_val : rev.val = arr.val.reverse)
        (hrev_lo : 1 ≤ rev.length) (hrev_hi : rev.length ≤ 100)
        (hrev_entries : ∀ i, i < rev.length → 1 ≤ entry rev i ∧ entry rev i ≤ 1000), ∀ r s : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays rev = ok s → r = s) := by
    sorry

  /-- Whenever the function returns r for arr and s for brr, r <= s.
    Preconditions: Both arr and brr satisfy 1 <= len(arr) = len(brr) = n <= 100 and entries in [1, 1000], and arr[i] <= brr[i] for every 0 <= i < n. -/
  theorem spec_8 (arr brr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
      (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
      (hentries_brr : ∀ i, i < brr.length → 1 ≤ entry brr i ∧ entry brr i ≤ 1000)
      (hle : ∀ i, i < arr.length → entry arr i ≤ entry brr i) :
      ∀ r s : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s → r.val ≤ s.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr brr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
        (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
        (hentries_brr : ∀ i, i < brr.length → 1 ≤ entry brr i ∧ entry brr i ≤ 1000)
        (hle : ∀ i, i < arr.length → entry arr i ≤ entry brr i), ∀ r s : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s → r.val ≤ s.val) := by
    sorry

  /-- Whenever the function returns r for arr and s for brr, s = k * r.
    Preconditions: arr satisfies 1 <= len(arr) <= 100 and entries in [1, 1000]. Let n = len(arr), let k be an integer with k >= 1, and let brr be a slice of length n with brr[i] = k * arr[i] for every 0 <= i < n, such that brr also satisfies 1 <= brr[i] <= 1000 for all i. -/
  theorem spec_9 (arr brr : Slice Std.I64) (k : ℤ)
      (hk : 1 ≤ k)
      (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
      (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
      (hentries_brr_lo : ∀ i, i < brr.length → 1 ≤ entry brr i)
      (hentries_brr_hi : ∀ i, i < brr.length → entry brr i ≤ 1000)
      (hscale : ∀ i, i < arr.length → entry brr i = k * entry arr i) :
      ∀ r s : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s →
        s.val = k * r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr brr : Slice Std.I64) (k : ℤ)
        (hk : 1 ≤ k)
        (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
        (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
        (hentries_brr_lo : ∀ i, i < brr.length → 1 ≤ entry brr i)
        (hentries_brr_hi : ∀ i, i < brr.length → entry brr i ≤ 1000)
        (hscale : ∀ i, i < arr.length → entry brr i = k * entry arr i), ∀ r s : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s →
          s.val = k * r.val) := by
    sorry

  /-- Whenever the function returns a result r, let n = len(arr) and let A(n) = sum over odd L with 1 <= L <= n of L * (n - L + 1). Then r >= A(n).
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100, and for every i with 0 <= i < len(arr), 1 <= arr[i] <= 1000. -/
  theorem spec_10 (arr : Slice Std.I64)
      (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
      (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000) :
      ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        A arr.length ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lo : 1 ≤ arr.length) (hlen_hi : arr.length ≤ 100)
        (hentries : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000), ∀ r : Std.I64, Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          A arr.length ≤ r.val) := by
    sorry

  /-- Whenever the function returns r for arr and s for brr, s = r + c * A(n), where A(n) = sum over odd L with 1 <= L <= n of L * (n - L + 1).
    Preconditions: arr and brr both satisfy 1 <= len(arr) = len(brr) = n <= 100 and entries in [1, 1000], and there is an integer c such that brr[i] = arr[i] + c for every 0 <= i < n. -/
  theorem spec_11 (arr brr : Slice Std.I64) (c : ℤ)
      (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
      (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
      (hentries_brr : ∀ i, i < brr.length → 1 ≤ entry brr i ∧ entry brr i ≤ 1000)
      (hshift : ∀ i, i < arr.length → entry brr i = entry arr i + c) :
      ∀ r s : Std.I64,
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
        Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s →
        s.val = r.val + c * A arr.length := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr brr : Slice Std.I64) (c : ℤ)
        (hlen_lo : 1 ≤ arr.length) (hlen_eq : arr.length = brr.length) (hlen_hi : arr.length ≤ 100)
        (hentries_arr : ∀ i, i < arr.length → 1 ≤ entry arr i ∧ entry arr i ≤ 1000)
        (hentries_brr : ∀ i, i < brr.length → 1 ≤ entry brr i ∧ entry brr i ≤ 1000)
        (hshift : ∀ i, i < arr.length → entry brr i = entry arr i + c), ∀ r s : Std.I64,
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays arr = ok r →
          Aegis.SumOddLengthSubarrays.sum_odd_length_subarrays brr = ok s →
          s.val = r.val + c * A arr.length) := by
    sorry

  end AegisSpec.SumOddLengthSubarrays
