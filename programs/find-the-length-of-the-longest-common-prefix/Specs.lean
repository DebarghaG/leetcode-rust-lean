import Aegis.LongestCommonPrefix.Code.Funs

/-!
# Specifications of `Aegis.LongestCommonPrefix.longest_common_prefix`

LeetCode problem `find-the-length-of-the-longest-common-prefix`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.LongestCommonPrefix

  open Aegis.LongestCommonPrefix

  def decDigitsOfNat (n : ℕ) : List ℕ :=
    if _ : n = 0 then []
    else if n < 10 then [n]
    else decDigitsOfNat (n / 10) ++ [n % 10]
  termination_by n

  def digitString (n : ℤ) : List ℕ := decDigitsOfNat n.toNat

  def digitCount (n : ℤ) : ℕ := (digitString n).length

  def digitAt (n : ℤ) (k : ℕ) : Option ℕ := (digitString n)[k]?

  def commonPrefixLen : List ℕ → List ℕ → ℕ
    | [], _ => 0
    | _ :: _, [] => 0
    | x :: xs, y :: ys => if x = y then 1 + commonPrefixLen xs ys else 0

  def lcp (a b : ℤ) : ℕ := commonPrefixLen (digitString a) (digitString b)

  def allPositive (s : Slice I64) : Prop := ∀ x ∈ s.val, 0 < x.val

  def valuesOf (s : Slice I64) : Set ℤ := {v | ∃ x ∈ s.val, x.val = v}

  def maxDigitCount (s : Slice I64) : ℕ :=
    s.val.foldr (fun x acc => max (digitCount x.val) acc) 0

  def maxLcp (s1 s2 : Slice I64) : ℕ :=
    s1.val.foldr (fun a acc => s2.val.foldr (fun b inner => max (lcp a.val b.val) inner) acc) 0

  /-- Whenever the function returns a result r, r equals max { LCP(arr1[i], arr2[j]) | 0 <= i < len(arr1) and 0 <= j < len(arr2) }. Equivalently, r is the largest k >= 0 such that some arr1[i] and arr2[j] share their first k decimal digits; if no pair shares a nonempty prefix, this maximum is 0.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For a positive integer n, let D(n) be its decimal digit string with no leading zeros, and let d(n) = len(D(n)). For positive a,b, let LCP(a,b) be the largest k with 0 <= k <= min(d(a),d(b)) such that the first k digits of D(a) and D(b) are equal; k=0 is always allowed and means no nonempty common prefix. -/
  theorem spec_1 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) :
      r.val = (maxLcp arr1 arr2 : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r), r.val = (maxLcp arr1 arr2 : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail (no arithmetic overflow, no out-of-bounds access, and no panic).
    Preconditions: 1 <= len(arr1) <= 50000; 1 <= len(arr2) <= 50000; for every i with 0 <= i < len(arr1), 1 <= arr1[i] <= 100000000; for every j with 0 <= j < len(arr2), 1 <= arr2[j] <= 100000000. -/
  theorem spec_2 (arr1 arr2 : Slice I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen1' : arr1.val.length ≤ 50000)
      (hlen2 : 1 ≤ arr2.val.length) (hlen2' : arr2.val.length ≤ 50000)
      (hrange1 : ∀ x ∈ arr1.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
      (hrange2 : ∀ x ∈ arr2.val, 1 ≤ x.val ∧ x.val ≤ 100000000) :
      ∃ r, longest_common_prefix arr1 arr2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr1 arr2 : Slice I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen1' : arr1.val.length ≤ 50000)
        (hlen2 : 1 ≤ arr2.val.length) (hlen2' : arr2.val.length ≤ 50000)
        (hrange1 : ∀ x ∈ arr1.val, 1 ≤ x.val ∧ x.val ≤ 100000000)
        (hrange2 : ∀ x ∈ arr2.val, 1 ≤ x.val ∧ x.val ≤ 100000000), ∃ r, longest_common_prefix arr1 arr2 = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= min( max_{0 <= i < len(arr1)} d(arr1[i]), max_{0 <= j < len(arr2)} d(arr2[j]) ).
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For positive n, d(n) is the number of decimal digits of n. -/
  theorem spec_3 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) :
      0 ≤ r.val ∧ r.val ≤ ((min (maxDigitCount arr1) (maxDigitCount arr2) : ℕ) : ℤ) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r), 0 ≤ r.val ∧ r.val ≤ ((min (maxDigitCount arr1) (maxDigitCount arr2) : ℕ) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(arr1) and every j with 0 <= j < len(arr2), LCP(arr1[i], arr2[j]) <= r.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For positive n, d(n) is the number of decimal digits of n; LCP(a,b) is the largest k with 0 <= k <= min(d(a),d(b)) and equal first k decimal digits. -/
  theorem spec_4 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) :
      ∀ a ∈ arr1.val, ∀ b ∈ arr2.val, (lcp a.val b.val : ℤ) ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r), ∀ a ∈ arr1.val, ∀ b ∈ arr2.val, (lcp a.val b.val : ℤ) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i and j with 0 <= i < len(arr1) and 0 <= j < len(arr2) such that arr1[i] and arr2[j] share their first r decimal digits; that is, LCP(arr1[i], arr2[j]) >= r.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For positive n, d(n) is the number of decimal digits of n; LCP(a,b) is the largest k with 0 <= k <= min(d(a),d(b)) and equal first k decimal digits. -/
  theorem spec_5 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) (hr : 0 < r.val) :
      ∃ a ∈ arr1.val, ∃ b ∈ arr2.val, r.val ≤ (lcp a.val b.val : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r) (hr : 0 < r.val), ∃ a ∈ arr1.val, ∃ b ∈ arr2.val, r.val ≤ (lcp a.val b.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, there exist indices i and j such that arr1[i] and arr2[j] share their first r decimal digits and, if r < min(d(arr1[i]), d(arr2[j])), then their (r+1)-st decimal digits differ.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For positive n, d(n) is the number of decimal digits of n. -/
  theorem spec_6 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) (hr : 0 < r.val) :
      ∃ a ∈ arr1.val, ∃ b ∈ arr2.val,
        r.val ≤ (lcp a.val b.val : ℤ) ∧
          (r.val < ((min (digitCount a.val) (digitCount b.val) : ℕ) : ℤ) →
            digitAt a.val r.val.toNat ≠ digitAt b.val r.val.toNat) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r) (hr : 0 < r.val), ∃ a ∈ arr1.val, ∃ b ∈ arr2.val,
          r.val ≤ (lcp a.val b.val : ℤ) ∧
            (r.val < ((min (digitCount a.val) (digitCount b.val) : ℕ) : ℤ) →
              digitAt a.val r.val.toNat ≠ digitAt b.val r.val.toNat)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < len(arr1) and every j with 0 <= j < len(arr2), the first decimal digit of arr1[i] is different from the first decimal digit of arr2[j].
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. -/
  theorem spec_7 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) :
      r.val = 0 ↔ ∀ a ∈ arr1.val, ∀ b ∈ arr2.val, digitAt a.val 0 ≠ digitAt b.val 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r), r.val = 0 ↔ ∀ a ∈ arr1.val, ∀ b ∈ arr2.val, digitAt a.val 0 ≠ digitAt b.val 0) := by
    sorry

  /-- Whenever the function returns a result r, if there exist i and j such that the decimal digit string D(arr1[i]) is a prefix of D(arr2[j]), then r >= d(arr1[i]); symmetrically, if D(arr2[j]) is a prefix of D(arr1[i]), then r >= d(arr2[j]).
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. For positive n, D(n) is its decimal digit string and d(n) = len(D(n)). -/
  theorem spec_8 (arr1 arr2 : Slice I64) (r : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r) :
      (∀ a ∈ arr1.val, ∀ b ∈ arr2.val,
          List.IsPrefix (digitString a.val) (digitString b.val) → (digitCount a.val : ℤ) ≤ r.val) ∧
        (∀ a ∈ arr1.val, ∀ b ∈ arr2.val,
          List.IsPrefix (digitString b.val) (digitString a.val) →
            (digitCount b.val : ℤ) ≤ r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r), (∀ a ∈ arr1.val, ∀ b ∈ arr2.val,
            List.IsPrefix (digitString a.val) (digitString b.val) → (digitCount a.val : ℤ) ≤ r.val) ∧
          (∀ a ∈ arr1.val, ∀ b ∈ arr2.val,
            List.IsPrefix (digitString b.val) (digitString a.val) →
              (digitCount b.val : ℤ) ≤ r.val)) := by
    sorry

  /-- For every slice arr1' that is a permutation of arr1 (same multiset of elements) and every slice arr2' that is a permutation of arr2, if the function returns r on (arr1, arr2) and returns r' on (arr1', arr2'), then r = r'.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. -/
  theorem spec_9 (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hperm1 : arr1'.val.Perm arr1.val) (hperm2 : arr2'.val.Perm arr2.val)
      (hres : longest_common_prefix arr1 arr2 = ok r)
      (hres' : longest_common_prefix arr1' arr2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hperm1 : arr1'.val.Perm arr1.val) (hperm2 : arr2'.val.Perm arr2.val)
        (hres : longest_common_prefix arr1 arr2 = ok r)
        (hres' : longest_common_prefix arr1' arr2' = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on (arr1, arr2) and returns r' on (arr2, arr1), then r = r'.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; for every i with 0 <= i < len(arr1), arr1[i] > 0; for every j with 0 <= j < len(arr2), arr2[j] > 0. -/
  theorem spec_10 (arr1 arr2 : Slice I64) (r r' : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hres : longest_common_prefix arr1 arr2 = ok r)
      (hres' : longest_common_prefix arr2 arr1 = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr1 arr2 : Slice I64) (r r' : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hres : longest_common_prefix arr1 arr2 = ok r)
        (hres' : longest_common_prefix arr2 arr1 = ok r'), r.val = r'.val) := by
    sorry

  /-- If the function returns r on (arr1, arr2) and returns r' on (arr1', arr2'), then r' >= r.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; len(arr1') >= 1; len(arr2') >= 1; all elements of arr1, arr2, arr1', arr2' are positive; the set of values occurring in arr1 is a subset of the set of values occurring in arr1'; the set of values occurring in arr2 is a subset of the set of values occurring in arr2'. -/
  theorem spec_11 (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hlen1' : 1 ≤ arr1'.val.length) (hlen2' : 1 ≤ arr2'.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hpos1' : allPositive arr1') (hpos2' : allPositive arr2')
      (hsub1 : valuesOf arr1 ⊆ valuesOf arr1') (hsub2 : valuesOf arr2 ⊆ valuesOf arr2')
      (hres : longest_common_prefix arr1 arr2 = ok r)
      (hres' : longest_common_prefix arr1' arr2' = ok r') :
      r.val ≤ r'.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hlen1' : 1 ≤ arr1'.val.length) (hlen2' : 1 ≤ arr2'.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hpos1' : allPositive arr1') (hpos2' : allPositive arr2')
        (hsub1 : valuesOf arr1 ⊆ valuesOf arr1') (hsub2 : valuesOf arr2 ⊆ valuesOf arr2')
        (hres : longest_common_prefix arr1 arr2 = ok r)
        (hres' : longest_common_prefix arr1' arr2' = ok r'), r.val ≤ r'.val) := by
    sorry

  /-- If the function returns r on (arr1, arr2) and returns r' on (arr1', arr2'), then r = r'.
    Preconditions: len(arr1) >= 1; len(arr2) >= 1; all elements of arr1 and arr2 are positive; arr1' is a slice whose set of values is exactly the set of values occurring in arr1, with each distinct value occurring once; arr2' is a slice whose set of values is exactly the set of values occurring in arr2, with each distinct value occurring once. -/
  theorem spec_12 (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
      (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
      (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
      (hset1 : valuesOf arr1' = valuesOf arr1) (hnd1 : arr1'.val.Nodup)
      (hset2 : valuesOf arr2' = valuesOf arr2) (hnd2 : arr2'.val.Nodup)
      (hres : longest_common_prefix arr1 arr2 = ok r)
      (hres' : longest_common_prefix arr1' arr2' = ok r') :
      r.val = r'.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr1 arr2 arr1' arr2' : Slice I64) (r r' : I64)
        (hlen1 : 1 ≤ arr1.val.length) (hlen2 : 1 ≤ arr2.val.length)
        (hpos1 : allPositive arr1) (hpos2 : allPositive arr2)
        (hset1 : valuesOf arr1' = valuesOf arr1) (hnd1 : arr1'.val.Nodup)
        (hset2 : valuesOf arr2' = valuesOf arr2) (hnd2 : arr2'.val.Nodup)
        (hres : longest_common_prefix arr1 arr2 = ok r)
        (hres' : longest_common_prefix arr1' arr2' = ok r'), r.val = r'.val) := by
    sorry

  end AegisSpec.LongestCommonPrefix
