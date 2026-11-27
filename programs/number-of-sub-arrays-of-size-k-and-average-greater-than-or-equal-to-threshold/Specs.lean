import Aegis.NumOfSubarrays.Code.Funs

/-!
# Specifications of `Aegis.NumOfSubarrays.num_of_subarrays`

LeetCode problem `number-of-sub-arrays-of-size-k-and-average-greater-than-or-equal-to-threshold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumOfSubarrays

  def elems (arr : Slice Std.I64) : List ℤ := arr.val.map (fun x => x.val)

  def InBounds (a : List ℤ) : Prop := ∀ x ∈ a, 1 ≤ x ∧ x ≤ 10000

  def win (a : List ℤ) (i : ℕ) (k : ℤ) : List ℤ := (a.drop i).take k.toNat

  def winSum (a : List ℤ) (i : ℕ) (k : ℤ) : ℤ := (win a i k).sum

  @[reducible] def winOk (a : List ℤ) (k t : ℤ) (i : ℕ) : Prop := t * k ≤ winSum a i k

  def starts (a : List ℤ) (k : ℤ) : List ℕ := List.range (a.length - k.toNat + 1)

  def countOk (a : List ℤ) (k t : ℤ) : ℕ :=
    (starts a k).countP (fun i => decide (winOk a k t i))

  def countBelow (a : List ℤ) (k t : ℤ) : ℕ :=
    (starts a k).countP (fun i => decide (winSum a i k < t * k))

  @[reducible] def winAllEq (a : List ℤ) (k v : ℤ) (i : ℕ) : Prop := ∀ x ∈ win a i k, x = v

  def Dominates (a b : List ℤ) : Prop :=
    List.Forall₂ (fun x y => 1 ≤ x ∧ x ≤ y ∧ y ≤ 10000) a b

  /-- For every input satisfying the preconditions, the function returns a result r and does not fail: there is no arithmetic overflow, panic, or out-of-bounds access.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_1 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∃ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∃ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of integers i such that 0 <= i <= len(arr) - k and sum_{j=0}^{k-1} arr[i+j] >= threshold * k. Equivalently, r is the number of contiguous sub-arrays of arr of length exactly k whose average is greater than or equal to threshold.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_2 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val = (countOk (elems arr) k.val threshold.val : ℤ) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val = (countOk (elems arr) k.val threshold.val : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= len(arr) - k + 1.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_3 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          0 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) - k.val + 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            0 ≤ r.val ∧ r.val ≤ (arr.val.length : ℤ) - k.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if sum_{i=0}^{len(arr)-1} arr[i] >= threshold * len(arr), and r = 0 otherwise.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k = len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_4 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : k.val = (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val =
            (if threshold.val * (arr.val.length : ℤ) ≤ (elems arr).sum then (1 : ℤ) else 0) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : k.val = (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val =
              (if threshold.val * (arr.val.length : ℤ) ≤ (elems arr).sum then (1 : ℤ) else 0)) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of indices i with 0 <= i < len(arr) and arr[i] >= threshold.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k = 1. threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_5 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : k.val = 1)
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val =
            (((elems arr).filter (fun x => decide (threshold.val ≤ x))).length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : k.val = 1)
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val =
              (((elems arr).filter (fun x => decide (threshold.val ≤ x))).length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(arr) - k + 1.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold = 0. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_6 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : threshold.val = 0) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val = (arr.val.length : ℤ) - k.val + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : threshold.val = 0), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val = (arr.val.length : ℤ) - k.val + 1) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000, and also arr[i] < threshold. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_7 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hlt : ∀ x ∈ elems arr, x < threshold.val)
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val = 0 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hlt : ∀ x ∈ elems arr, x < threshold.val)
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an integer i with 0 <= i <= len(arr) - k such that sum_{j=0}^{k-1} arr[i+j] >= threshold * k.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_8 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          (0 < r.val ↔
            ∃ i : ℕ, i ≤ arr.val.length - k.val.toNat ∧
              winOk (elems arr) k.val threshold.val i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            (0 < r.val ↔
              ∃ i : ℕ, i ≤ arr.val.length - k.val.toNat ∧
                winOk (elems arr) k.val threshold.val i)) := by
    sorry

  /-- Whenever the function returns a result r, r = len(arr) - k + 1 if and only if for every integer i with 0 <= i <= len(arr) - k, sum_{j=0}^{k-1} arr[i+j] >= threshold * k.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_9 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          (r.val = (arr.val.length : ℤ) - k.val + 1 ↔
            ∀ i : ℕ, i ≤ arr.val.length - k.val.toNat →
              winOk (elems arr) k.val threshold.val i) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            (r.val = (arr.val.length : ℤ) - k.val + 1 ↔
              ∀ i : ℕ, i ≤ arr.val.length - k.val.toNat →
                winOk (elems arr) k.val threshold.val i)) := by
    sorry

  /-- Whenever num_of_subarrays(arr, k, t1) returns r1 and num_of_subarrays(arr, k, t2) returns r2, we have r1 >= r2.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). t1 and t2 are integers with 0 <= t1 <= t2 <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_10 (arr : Slice Std.I64) (k t1 t2 : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ t1.val ∧ t1.val ≤ t2.val ∧ t2.val ≤ 10000) :
      ∀ r1 r2 : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k t1 = ok r1 →
          Aegis.NumOfSubarrays.num_of_subarrays arr k t2 = ok r2 →
            r2.val ≤ r1.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (arr : Slice Std.I64) (k t1 t2 : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ t1.val ∧ t1.val ≤ t2.val ∧ t2.val ≤ 10000), ∀ r1 r2 : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k t1 = ok r1 →
            Aegis.NumOfSubarrays.num_of_subarrays arr k t2 = ok r2 →
              r2.val ≤ r1.val) := by
    sorry

  /-- Whenever num_of_subarrays(arr1, k, threshold) returns r1 and num_of_subarrays(arr2, k, threshold) returns r2, we have r1 <= r2.
    Preconditions: arr1 and arr2 are arrays of the same length n, where 1 <= n <= 100000. For every i with 0 <= i < n, 1 <= arr1[i] <= arr2[i] <= 10000. k is an integer with 1 <= k <= n. threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_11 (arr1 arr2 : Slice Std.I64) (k threshold : Std.I64)
      (hn : 1 ≤ arr1.val.length) (hn_max : arr1.val.length ≤ 100000)
      (hdom : Dominates (elems arr1) (elems arr2))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr1.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r1 r2 : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr1 k threshold = ok r1 →
          Aegis.NumOfSubarrays.num_of_subarrays arr2 k threshold = ok r2 →
            r1.val ≤ r2.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (arr1 arr2 : Slice Std.I64) (k threshold : Std.I64)
        (hn : 1 ≤ arr1.val.length) (hn_max : arr1.val.length ≤ 100000)
        (hdom : Dominates (elems arr1) (elems arr2))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr1.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r1 r2 : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr1 k threshold = ok r1 →
            Aegis.NumOfSubarrays.num_of_subarrays arr2 k threshold = ok r2 →
              r1.val ≤ r2.val) := by
    sorry

  /-- Let rev(arr) be the array of length len(arr) with rev(arr)[i] = arr[len(arr)-1-i] for 0 <= i < len(arr). Whenever num_of_subarrays(arr, k, threshold) returns r and num_of_subarrays(rev(arr), k, threshold) returns r', we have r' = r.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_12 (arr rev : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000)
      (hrev : rev.val = arr.val.reverse) :
      ∀ r r' : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          Aegis.NumOfSubarrays.num_of_subarrays rev k threshold = ok r' →
            r'.val = r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (arr rev : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000)
        (hrev : rev.val = arr.val.reverse), ∀ r r' : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            Aegis.NumOfSubarrays.num_of_subarrays rev k threshold = ok r' →
              r'.val = r.val) := by
    sorry

  /-- Whenever num_of_subarrays(arr, k, threshold) returns r and num_of_subarrays(arr', k, threshold') returns r', we have r' = r.
    Preconditions: arr, k, and threshold satisfy the common constraints: 1 <= len(arr) <= 100000; for every i with 0 <= i < len(arr), 1 <= arr[i] <= 10000; 1 <= k <= len(arr); 0 <= threshold <= 10000. Let c be an integer and define arr' by arr'[i] = arr[i] + c for every i with 0 <= i < len(arr). Assume 1 <= arr'[i] <= 10000 for every such i, and 0 <= threshold + c <= 10000. Let threshold' = threshold + c. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_13 (arr arr' : Slice Std.I64) (k threshold threshold' : Std.I64) (c : ℤ)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000)
      (hshift : elems arr' = (elems arr).map (fun x => x + c))
      (hval' : InBounds (elems arr'))
      (hthr'_val : threshold'.val = threshold.val + c)
      (hthr' : 0 ≤ threshold'.val ∧ threshold'.val ≤ 10000) :
      ∀ r r' : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          Aegis.NumOfSubarrays.num_of_subarrays arr' k threshold' = ok r' →
            r'.val = r.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (arr arr' : Slice Std.I64) (k threshold threshold' : Std.I64) (c : ℤ)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000)
        (hshift : elems arr' = (elems arr).map (fun x => x + c))
        (hval' : InBounds (elems arr'))
        (hthr'_val : threshold'.val = threshold.val + c)
        (hthr' : 0 ≤ threshold'.val ∧ threshold'.val ≤ 10000), ∀ r r' : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            Aegis.NumOfSubarrays.num_of_subarrays arr' k threshold' = ok r' →
              r'.val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, r equals the number of integers i with 0 <= i <= len(arr) - k such that arr[i+j] = 10000 for every j with 0 <= j < k.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold = 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_14 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : threshold.val = 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val =
            ((starts (elems arr) k.val).countP
              (fun i => decide (winAllEq (elems arr) k.val 10000 i)) : ℤ) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : threshold.val = 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val =
              ((starts (elems arr) k.val).countP
                (fun i => decide (winAllEq (elems arr) k.val 10000 i)) : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r and there is an integer i with 0 <= i <= len(arr) - k and sum_{j=0}^{k-1} arr[i+j] = threshold * k, we have r >= 1: a sub-array whose average equals the threshold exactly is counted, i.e. the comparison is >= and not >.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_15 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          (∃ i : ℕ, i ≤ arr.val.length - k.val.toNat ∧
              winSum (elems arr) i k.val = threshold.val * k.val) →
            1 ≤ r.val := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            (∃ i : ℕ, i ≤ arr.val.length - k.val.toNat ∧
                winSum (elems arr) i k.val = threshold.val * k.val) →
              1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = (len(arr) - k + 1) - #{ i : 0 <= i <= len(arr) - k and sum_{j=0}^{k-1} arr[i+j] < threshold * k }, i.e. the qualifying and the non-qualifying length-k sub-arrays together exhaust all len(arr) - k + 1 sub-arrays of length k.
    Preconditions: len(arr) is an integer with 1 <= len(arr) <= 100000. For every i with 0 <= i < len(arr), arr[i] is an integer with 1 <= arr[i] <= 10000. k is an integer with 1 <= k <= len(arr). threshold is an integer with 0 <= threshold <= 10000. All arithmetic in this specification is mathematical integer arithmetic. -/
  theorem spec_16 (arr : Slice Std.I64) (k threshold : Std.I64)
      (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
      (hval : InBounds (elems arr))
      (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
      (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000) :
      ∀ r : Std.I64,
        Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
          r.val =
            ((arr.val.length : ℤ) - k.val + 1) -
              (countBelow (elems arr) k.val threshold.val : ℤ) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (arr : Slice Std.I64) (k threshold : Std.I64)
        (hlen : 1 ≤ arr.val.length) (hlen_max : arr.val.length ≤ 100000)
        (hval : InBounds (elems arr))
        (hk : 1 ≤ k.val ∧ k.val ≤ (arr.val.length : ℤ))
        (hthr : 0 ≤ threshold.val ∧ threshold.val ≤ 10000), ∀ r : Std.I64,
          Aegis.NumOfSubarrays.num_of_subarrays arr k threshold = ok r →
            r.val =
              ((arr.val.length : ℤ) - k.val + 1) -
                (countBelow (elems arr) k.val threshold.val : ℤ)) := by
    sorry

  end AegisSpec.NumOfSubarrays
