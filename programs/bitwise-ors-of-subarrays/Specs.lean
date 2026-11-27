import Aegis.SubarrayBitwiseORs.Code.Funs

/-!
# Specifications of `Aegis.SubarrayBitwiseORs.subarray_bitwise_o_rs`

LeetCode problem `bitwise-ors-of-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.SubarrayBitwiseORs

  open Aegis.SubarrayBitwiseORs

  def vals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def bor (a b : ℤ) : ℤ := ((a.toNat ||| b.toNat : ℕ) : ℤ)

  def band (a b : ℤ) : ℤ := ((a.toNat &&& b.toNat : ℕ) : ℤ)

  def listOr (l : List ℤ) : ℤ := l.foldl bor 0

  def entry (l : List Std.I64) (i : ℕ) : Option ℤ := (l[i]?).map (fun x => x.val)

  def segOr (arr : Slice Std.I64) (i j : ℕ) : ℤ :=
    listOr (((vals arr).drop i).take (j + 1 - i))

  def subarrayORs (arr : Slice Std.I64) : Set ℤ :=
    {v | ∃ i j : ℕ, i ≤ j ∧ j < arr.val.length ∧ v = segOr arr i j}

  def elemVals (arr : Slice Std.I64) : Set ℤ :=
    {v | ∃ (i : ℕ) (_h : i < arr.val.length), (arr.val[i]).val = v}

  def numSubarrays (n : ℕ) : ℕ := n * (n + 1) / 2

  /-- Let n = len(arr), and let O = { v | there exist integers i and j with 0 <= i <= j < n and v = arr[i] OR arr[i+1] OR ... OR arr[j] }, where OR is bitwise OR on non-negative integers. Whenever the function returns a result r, the mathematical integer value of r equals |O|, the number of distinct bitwise ORs of all non-empty contiguous subarrays of arr, counting each distinct value once.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000, where arr[i] denotes the mathematical integer value of the i-th 64-bit element. All indices are 0-based. -/
  theorem spec_1
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000) :
      ∀ r : Std.I64,
        subarray_bitwise_o_rs arr = ok r → r.val = ((subarrayORs arr).ncard : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000), ∀ r : Std.I64,
          subarray_bitwise_o_rs arr = ok r → r.val = ((subarrayORs arr).ncard : ℤ)) := by
    sorry

  /-- The function returns a result r and does not fail: for every arr satisfying the preconditions, there is no overflow, out-of-bounds access, panic, or other failure.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000, where arr[i] denotes the mathematical integer value of the i-th 64-bit element. All indices are 0-based. -/
  theorem spec_2
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000) :
      ∃ r : Std.I64, subarray_bitwise_o_rs arr = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000), ∃ r : Std.I64, subarray_bitwise_o_rs arr = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= |{ x | there exists an integer i with 0 <= i < len(arr) and x = arr[i] }|, the number of distinct values that occur as elements of arr.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000. All indices are 0-based. -/
  theorem spec_3
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000) :
      ∀ r : Std.I64,
        subarray_bitwise_o_rs arr = ok r → ((elemVals arr).ncard : ℤ) ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000), ∀ r : Std.I64,
          subarray_bitwise_o_rs arr = ok r → ((elemVals arr).ncard : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= len(arr) * (len(arr) + 1) / 2, the number of non-empty contiguous subarrays of arr.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000. All indices are 0-based. -/
  theorem spec_4
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000) :
      ∀ r : Std.I64,
        subarray_bitwise_o_rs arr = ok r →
          r.val ≤ ((numSubarrays arr.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000), ∀ r : Std.I64,
          subarray_bitwise_o_rs arr = ok r →
            r.val ≤ ((numSubarrays arr.val.length : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r <= 31 * len(arr).
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000. All indices are 0-based. -/
  theorem spec_5
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000) :
      ∀ r : Std.I64,
        subarray_bitwise_o_rs arr = ok r → r.val ≤ 31 * (arr.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000), ∀ r : Std.I64,
          subarray_bitwise_o_rs arr = ok r → r.val ≤ 31 * (arr.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(arr) * (len(arr) + 1) / 2.
    Preconditions: len(arr) >= 1, for every i with 0 <= i < len(arr), 0 < arr[i] <= 1000000000, and for every i,j with 0 <= i < j < len(arr), (arr[i] AND arr[j]) = 0 using bitwise AND. All indices are 0-based. -/
  theorem spec_6
      (arr : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hpositive : ∀ (i : ℕ) (h : i < arr.val.length),
        0 < (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
      (hdisjoint : ∀ (i j : ℕ) (hij : i < j) (hj : j < arr.val.length),
        band (arr.val[i]).val (arr.val[j]).val = 0) :
      ∀ r : Std.I64,
        subarray_bitwise_o_rs arr = ok r →
          r.val = ((numSubarrays arr.val.length : ℕ) : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hpositive : ∀ (i : ℕ) (h : i < arr.val.length),
          0 < (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
        (hdisjoint : ∀ (i j : ℕ) (hij : i < j) (hj : j < arr.val.length),
          band (arr.val[i]).val (arr.val[j]).val = 0), ∀ r : Std.I64,
          subarray_bitwise_o_rs arr = ok r →
            r.val = ((numSubarrays arr.val.length : ℕ) : ℤ)) := by
    sorry

  /-- If the function returns result r on arr and result q on rev, then r = q.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 50000, and for every i with 0 <= i < len(arr), 0 <= arr[i] <= 1000000000. Let rev be the slice with len(rev) = len(arr) and rev[i] = arr[len(arr)-1-i] for every 0 <= i < len(arr). All indices are 0-based. -/
  theorem spec_7
      (arr rev : Slice Std.I64)
      (hlen_lower : 1 ≤ arr.val.length)
      (hlen_upper : arr.val.length ≤ 50000)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
      (hrev : rev.val = arr.val.reverse) :
      ∀ r q : Std.I64,
        subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs rev = ok q → r = q := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr rev : Slice Std.I64)
        (hlen_lower : 1 ≤ arr.val.length)
        (hlen_upper : arr.val.length ≤ 50000)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
        (hrev : rev.val = arr.val.reverse), ∀ r q : Std.I64,
          subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs rev = ok q → r = q) := by
    sorry

  /-- If the function returns result r on arr and result q on b, then r <= q.
    Preconditions: arr and b are slices satisfying the input constraints: 1 <= len(arr) <= 50000, 1 <= len(b) <= 50000, all entries are between 0 and 1000000000 inclusive, and all indices are 0-based. In addition, there exists an integer s with 0 <= s and s + len(arr) <= len(b) such that for every i with 0 <= i < len(arr), arr[i] = b[s+i]. -/
  theorem spec_8
      (arr b : Slice Std.I64)
      (harr_lower : 1 ≤ arr.val.length)
      (harr_upper : arr.val.length ≤ 50000)
      (harr_entries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
      (hb_lower : 1 ≤ b.val.length)
      (hb_upper : b.val.length ≤ 50000)
      (hb_entries : ∀ (i : ℕ) (h : i < b.val.length),
        0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 1000000000)
      (hembed : ∃ s : ℕ,
        s + arr.val.length ≤ b.val.length ∧
          ∀ (i : ℕ) (h : i < arr.val.length), entry arr.val i = entry b.val (s + i)) :
      ∀ r q : Std.I64,
        subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs b = ok q →
          r.val ≤ q.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr b : Slice Std.I64)
        (harr_lower : 1 ≤ arr.val.length)
        (harr_upper : arr.val.length ≤ 50000)
        (harr_entries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
        (hb_lower : 1 ≤ b.val.length)
        (hb_upper : b.val.length ≤ 50000)
        (hb_entries : ∀ (i : ℕ) (h : i < b.val.length),
          0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 1000000000)
        (hembed : ∃ s : ℕ,
          s + arr.val.length ≤ b.val.length ∧
            ∀ (i : ℕ) (h : i < arr.val.length), entry arr.val i = entry b.val (s + i)), ∀ r q : Std.I64,
          subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs b = ok q →
            r.val ≤ q.val) := by
    sorry

  /-- If the function returns result r on arr and result q on arr2, then r = q.
    Preconditions: arr satisfies len(arr) <= 49999 and all original entry bounds 0 <= arr[i] <= 1000000000 for 0 <= i < len(arr). Let n = len(arr). Let arr2 be a slice with len(arr2) = n+1 for which there exists an integer k with 0 <= k < n such that arr2[i] = arr[i] for 0 <= i <= k, arr2[k+1] = arr[k], and arr2[i] = arr[i-1] for k+2 <= i <= n. All indices are 0-based. -/
  theorem spec_9
      (arr arr2 : Slice Std.I64)
      (hlen : arr.val.length ≤ 49999)
      (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
        0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
      (hlen2 : arr2.val.length = arr.val.length + 1)
      (hinsert : ∃ k : ℕ,
        k < arr.val.length ∧
          (∀ (i : ℕ) (h : i ≤ k), entry arr2.val i = entry arr.val i) ∧
          entry arr2.val (k + 1) = entry arr.val k ∧
          (∀ (i : ℕ) (h₁ : k + 2 ≤ i) (h₂ : i ≤ arr.val.length),
            entry arr2.val i = entry arr.val (i - 1))) :
      ∀ r q : Std.I64,
        subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs arr2 = ok q → r = q := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr arr2 : Slice Std.I64)
        (hlen : arr.val.length ≤ 49999)
        (hentries : ∀ (i : ℕ) (h : i < arr.val.length),
          0 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 1000000000)
        (hlen2 : arr2.val.length = arr.val.length + 1)
        (hinsert : ∃ k : ℕ,
          k < arr.val.length ∧
            (∀ (i : ℕ) (h : i ≤ k), entry arr2.val i = entry arr.val i) ∧
            entry arr2.val (k + 1) = entry arr.val k ∧
            (∀ (i : ℕ) (h₁ : k + 2 ≤ i) (h₂ : i ≤ arr.val.length),
              entry arr2.val i = entry arr.val (i - 1))), ∀ r q : Std.I64,
          subarray_bitwise_o_rs arr = ok r → subarray_bitwise_o_rs arr2 = ok q → r = q) := by
    sorry

  end AegisSpec.SubarrayBitwiseORs
