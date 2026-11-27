import Aegis.KConcatenationMaxSum.Code.Funs

/-!
# Specifications of `Aegis.KConcatenationMaxSum.k_concatenation_max_sum`

LeetCode problem `k-concatenation-maximum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.KConcatenationMaxSum

  open Aegis.KConcatenationMaxSum

  def modulus : ℤ := 1000000007

  def sliceVals (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def subarraySum (l : List ℤ) (p q : ℕ) : ℤ := ((l.take (q + 1)).drop p).sum

  def subarraySums (l : List ℤ) : List ℤ :=
    (List.range l.length).flatMap fun p =>
      (List.range l.length).map fun q => subarraySum l p q

  def maxSubarraySum (l : List ℤ) : ℤ := (subarraySums l).foldr max 0

  def replicateConcat (l : List ℤ) (k : ℕ) : List ℤ := (List.range k).flatMap fun _ => l

  def prefixSums (l : List ℤ) : List ℤ := (List.range l.length).map fun j => (l.take (j + 1)).sum

  def suffixSums (l : List ℤ) : List ℤ := (List.range l.length).map fun i => (l.drop i).sum

  def maxZero (l : List ℤ) : ℤ := l.foldr max 0

  def prefMax (l : List ℤ) : ℤ := maxZero (prefixSums l)

  def sufMax (l : List ℤ) : ℤ := maxZero (suffixSums l)

  def posSum (l : List ℤ) : ℤ := (l.filter (fun x => 0 < x)).sum

  def totalSum (l : List ℤ) : ℤ := l.sum

  /-- Let n = len(arr), let B be the list of length n*k with B[t] = arr[t mod n] for 0 <= t < n*k, and let S = max(0, max{ sum_{t=p}^{q} B[t] | 0 <= p <= q < n*k }). Let M = 1000000007. The function returns a result r such that 0 <= r < M and r is congruent to S modulo M; equivalently r = S mod M.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
  theorem spec_1 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000) :
      ∃ r : Std.I64,
        k_concatenation_max_sum arr k = ok r ∧
          r.val = maxSubarraySum (replicateConcat (sliceVals arr) k.val.toNat) % modulus := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000), ∃ r : Std.I64,
          k_concatenation_max_sum arr k = ok r ∧
            r.val = maxSubarraySum (replicateConcat (sliceVals arr) k.val.toNat) % modulus) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not fail due to overflow, out-of-bounds access, or panic.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
  theorem spec_2 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000) :
      ∃ r : Std.I64, k_concatenation_max_sum arr k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000), ∃ r : Std.I64, k_concatenation_max_sum arr k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r < 1000000007.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
  theorem spec_3 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000) :
      ∀ r : Std.I64, k_concatenation_max_sum arr k = ok r → 0 ≤ r.val ∧ r.val < modulus := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000), ∀ r : Std.I64, k_concatenation_max_sum arr k = ok r → 0 ≤ r.val ∧ r.val < modulus) := by
    sorry

  /-- Let M1 = max(0, max{ sum_{i=p}^{q} arr[i] | 0 <= p <= q < len(arr) }). The function returns a result r with r = M1.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and k = 1. -/
  theorem spec_4 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hk_one : k.val = 1) :
      ∃ r : Std.I64,
        k_concatenation_max_sum arr k = ok r ∧ r.val = maxSubarraySum (sliceVals arr) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hk_one : k.val = 1), ∃ r : Std.I64,
          k_concatenation_max_sum arr k = ok r ∧ r.val = maxSubarraySum (sliceVals arr)) := by
    sorry

  /-- The function returns 0.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and arr[i] <= 0 for every i with 0 <= i < len(arr). -/
  theorem spec_5 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hnonpos : ∀ (i : ℕ) (h : i < arr.val.length), (arr.val[i]).val ≤ 0) :
      ∃ r : Std.I64, k_concatenation_max_sum arr k = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hnonpos : ∀ (i : ℕ) (h : i < arr.val.length), (arr.val[i]).val ≤ 0), ∃ r : Std.I64, k_concatenation_max_sum arr k = ok r ∧ r.val = 0) := by
    sorry

  /-- Let T = sum_{i=0}^{len(arr)-1} arr[i]. The function returns a result r with r = (k * T) mod 1000000007.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and arr[i] >= 0 for every i with 0 <= i < len(arr). -/
  theorem spec_6 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hnonneg : ∀ (i : ℕ) (h : i < arr.val.length), 0 ≤ (arr.val[i]).val) :
      ∃ r : Std.I64,
        k_concatenation_max_sum arr k = ok r ∧
          r.val = (k.val * (sliceVals arr).sum) % modulus := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hnonneg : ∀ (i : ℕ) (h : i < arr.val.length), 0 ≤ (arr.val[i]).val), ∃ r : Std.I64,
          k_concatenation_max_sum arr k = ok r ∧
            r.val = (k.val * (sliceVals arr).sum) % modulus) := by
    sorry

  /-- Let n = len(arr), T = sum_{i=0}^{n-1} arr[i] (so T <= 0), M1 = max(0, max{ sum_{t=p}^{q} arr[t] | 0 <= p <= q < n }), Pref = max(0, max{ sum_{t=0}^{j} arr[t] | 0 <= j < n }), and Suf = max(0, max{ sum_{t=i}^{n-1} arr[t] | 0 <= i < n }). The function returns a result r with r = (max(M1, Pref + Suf) mod 1000000007).
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), k >= 2, and T <= 0 where T = sum_{i=0}^{len(arr)-1} arr[i]. -/
  theorem spec_7 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hk_two : 2 ≤ k.val) (hT : (sliceVals arr).sum ≤ 0) :
      ∃ r : Std.I64,
        k_concatenation_max_sum arr k = ok r ∧
          r.val = (max (maxSubarraySum (sliceVals arr))
            (prefMax (sliceVals arr) + sufMax (sliceVals arr))) % modulus := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hk_two : 2 ≤ k.val) (hT : (sliceVals arr).sum ≤ 0), ∃ r : Std.I64,
          k_concatenation_max_sum arr k = ok r ∧
            r.val = (max (maxSubarraySum (sliceVals arr))
              (prefMax (sliceVals arr) + sufMax (sliceVals arr))) % modulus) := by
    sorry

  /-- Let n = len(arr), T = sum_{i=0}^{n-1} arr[i] (so T > 0), Pref = max{ sum_{t=0}^{j} arr[t] | 0 <= j < n }, and Suf = max{ sum_{t=i}^{n-1} arr[t] | 0 <= i < n }. The function returns a result r with r = ((Suf + (k - 2) * T + Pref) mod 1000000007).
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), k >= 2, and T > 0 where T = sum_{i=0}^{len(arr)-1} arr[i]. -/
  theorem spec_8 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hk_two : 2 ≤ k.val) (hT : 0 < (sliceVals arr).sum) :
      ∃ r : Std.I64,
        k_concatenation_max_sum arr k = ok r ∧
          r.val = (sufMax (sliceVals arr) + (k.val - 2) * (sliceVals arr).sum +
            prefMax (sliceVals arr)) % modulus := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hk_two : 2 ≤ k.val) (hT : 0 < (sliceVals arr).sum), ∃ r : Std.I64,
          k_concatenation_max_sum arr k = ok r ∧
            r.val = (sufMax (sliceVals arr) + (k.val - 2) * (sliceVals arr).sum +
              prefMax (sliceVals arr)) % modulus) := by
    sorry

  /-- Let B be the list of length len(arr)*k with B[t] = arr[t mod len(arr)] for 0 <= t < len(arr)*k. Whenever the function returns a result r with 0 < r < 1000000007, there exists a nonempty contiguous subarray of B whose sum is positive and congruent to r modulo 1000000007.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, and -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr). -/
  theorem spec_9 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000) :
      ∀ r : Std.I64,
        k_concatenation_max_sum arr k = ok r → 0 < r.val → r.val < modulus →
          ∃ (p q : ℕ),
            p ≤ q ∧ q < (replicateConcat (sliceVals arr) k.val.toNat).length ∧
              0 < subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q ∧
              subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q % modulus = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000), ∀ r : Std.I64,
          k_concatenation_max_sum arr k = ok r → 0 < r.val → r.val < modulus →
            ∃ (p q : ℕ),
              p ≤ q ∧ q < (replicateConcat (sliceVals arr) k.val.toNat).length ∧
                0 < subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q ∧
                subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q % modulus = r.val) := by
    sorry

  /-- Let B be the list of length len(arr)*k with B[t] = arr[t mod len(arr)] for 0 <= t < len(arr)*k. If the function returns r = 0, then there exists a nonempty contiguous subarray of B whose sum is a positive multiple of 1000000007.
    Preconditions: len(arr) >= 1, len(arr) <= 100000, 1 <= k <= 100000, -10000 <= arr[i] <= 10000 for every i with 0 <= i < len(arr), and there exists i with 0 <= i < len(arr) and arr[i] > 0. -/
  theorem spec_10 (arr : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
      (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
      (hpos : ∃ (i : ℕ), ∃ (h : i < arr.val.length), 0 < (arr.val[i]).val) :
      ∀ r : Std.I64,
        k_concatenation_max_sum arr k = ok r → r.val = 0 →
          ∃ (p q : ℕ),
            p ≤ q ∧ q < (replicateConcat (sliceVals arr) k.val.toNat).length ∧
              0 < subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q ∧
              modulus ∣ subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ arr.val.length) (hlen_le : arr.val.length ≤ 100000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000)
        (hval : ∀ (i : ℕ) (h : i < arr.val.length), -10000 ≤ (arr.val[i]).val ∧ (arr.val[i]).val ≤ 10000)
        (hpos : ∃ (i : ℕ), ∃ (h : i < arr.val.length), 0 < (arr.val[i]).val), ∀ r : Std.I64,
          k_concatenation_max_sum arr k = ok r → r.val = 0 →
            ∃ (p q : ℕ),
              p ≤ q ∧ q < (replicateConcat (sliceVals arr) k.val.toNat).length ∧
                0 < subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q ∧
                modulus ∣ subarraySum (replicateConcat (sliceVals arr) k.val.toNat) p q) := by
    sorry

  end AegisSpec.KConcatenationMaxSum
