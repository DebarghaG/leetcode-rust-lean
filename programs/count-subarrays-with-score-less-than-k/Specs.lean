import Aegis.CountSubarrays.Code.Funs

/-!
# Specifications of `Aegis.CountSubarrays.count_subarrays`

LeetCode problem `count-subarrays-with-score-less-than-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.CountSubarrays

def sliceVals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : Nat) : Int := (sliceVals nums).getD i 0

def subarraySum (l : List Int) (i j : Nat) : Int := ((l.drop i).take (j + 1 - i)).sum

def suffixSum (l : List Int) (i : Nat) : Int := (l.drop i).sum

abbrev qualifies (l : List Int) (k : Int) (i j : Nat) : Prop :=
  subarraySum l i j * ((j : Int) - (i : Int) + 1) < k

def numQualifying (l : List Int) (k : Int) : Nat :=
  ((Finset.product (Finset.range l.length) (Finset.range l.length)).filter
      (fun p => p.1 ≤ p.2 ∧ p.2 < l.length ∧ qualifies l k p.1 p.2)).card

def numEqual (l : List Int) (k : Int) : Nat :=
  ((Finset.product (Finset.range l.length) (Finset.range l.length)).filter
      (fun p => p.1 ≤ p.2 ∧ p.2 < l.length ∧
        subarraySum l p.1 p.2 * ((p.2 : Int) - (p.1 : Int) + 1) = k)).card

def numSingles (l : List Int) (k : Int) : Nat :=
  ((Finset.range l.length).filter (fun i => l.getD i 0 < k)).card

def numNewEndingAt (l : List Int) (x k : Int) : Nat :=
  ((Finset.range (l.length + 1)).filter
      (fun i => (suffixSum l i + x) * ((l.length : Int) - (i : Int) + 1) < k)).card

def sqrtPred (k : Int) : Nat := (k - 1).toNat.sqrt

def allOnesCount (n : Nat) (k : Int) : Nat :=
  Finset.sum (Finset.Icc 1 (min n (sqrtPred k))) (fun L => n - L + 1)

def totalPairs (n : Nat) : Nat := n * (n + 1) / 2

/-- Whenever count_subarrays(nums, k) returns a result r, r equals the number of integer pairs (i, j) such that 0 <= i <= j < n and (sum_{t=i}^{j} nums[t]) * (j - i + 1) < k.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      r.val = (numQualifying (sliceVals nums) k.val : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      r.val = (numQualifying (sliceVals nums) k.val : Int)) := by
  sorry

/-- The function count_subarrays(nums, k) returns a result r; it does not fail.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r) := by
  sorry

/-- Whenever count_subarrays(nums, k) returns a result r, 0 <= r <= n * (n + 1) / 2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs nums.val.length : Int)) := by
  sorry

/-- The function count_subarrays(nums, k) returns a result r and r = 1 if nums[0] < k, and r = 0 otherwise.
  Preconditions: Let n = len(nums). Assume n = 1, 1 <= nums[0] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 1)
    (hnum : 1 ≤ elem nums 0 ∧ elem nums 0 ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (if elem nums 0 < k.val then (1 : Int) else 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 1)
    (hnum : 1 ≤ elem nums 0 ∧ elem nums 0 ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (if elem nums 0 < k.val then (1 : Int) else 0)) := by
  sorry

/-- The function count_subarrays(nums, k) returns a result r and r = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, 1 <= k <= 1000000000000000, and for every i with 0 <= i < n we have nums[i] >= k. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hge : ∀ i, i < nums.val.length → elem nums i ≥ k.val) :
    ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧ r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hge : ∀ i, i < nums.val.length → elem nums i ≥ k.val), ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧ r.val = 0) := by
  sorry

/-- The function count_subarrays(nums, k) returns a result r and r = n * (n + 1) / 2.
  Preconditions: Let n = len(nums) and total = sum_{t=0}^{n-1} nums[t]. Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, 1 <= k <= 1000000000000000, and k > n * total. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hbig : k.val > (nums.val.length : Int) * (sliceVals nums).sum) :
    ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (totalPairs nums.val.length : Int) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hbig : k.val > (nums.val.length : Int) * (sliceVals nums).sum), ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (totalPairs nums.val.length : Int)) := by
  sorry

/-- Whenever count_subarrays(nums, k) returns a result r, r is at least the number of indices i with 0 <= i < n and nums[i] < k.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      (numSingles (sliceVals nums) k.val : Int) ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      (numSingles (sliceVals nums) k.val : Int) ≤ r.val) := by
  sorry

/-- If count_subarrays(nums, k1) returns r1 and count_subarrays(nums, k2) returns r2, then r1 <= r2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k1 <= k2 <= 1000000000000000. -/
theorem spec_8 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 1 ≤ k1.val) (hkk : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000000000) :
    ∀ r1 r2, Aegis.CountSubarrays.count_subarrays nums k1 = ok r1 →
      Aegis.CountSubarrays.count_subarrays nums k2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk1 : 1 ≤ k1.val) (hkk : k1.val ≤ k2.val) (hk2 : k2.val ≤ 1000000000000000), ∀ r1 r2, Aegis.CountSubarrays.count_subarrays nums k1 = ok r1 →
      Aegis.CountSubarrays.count_subarrays nums k2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- If count_subarrays(nums1, k) returns r1 and count_subarrays(nums2, k) returns r2, then r1 >= r2.
  Preconditions: Let n = len(nums1) = len(nums2). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums1[i] <= nums2[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums1.val.length) (hlen : nums1.val.length = nums2.val.length)
    (hn' : nums1.val.length ≤ 100000)
    (hnum : ∀ i, i < nums1.val.length →
      1 ≤ elem nums1 i ∧ elem nums1 i ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∀ r1 r2, Aegis.CountSubarrays.count_subarrays nums1 k = ok r1 →
      Aegis.CountSubarrays.count_subarrays nums2 k = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums1.val.length) (hlen : nums1.val.length = nums2.val.length)
    (hn' : nums1.val.length ≤ 100000)
    (hnum : ∀ i, i < nums1.val.length →
      1 ≤ elem nums1 i ∧ elem nums1 i ≤ elem nums2 i ∧ elem nums2 i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∀ r1 r2, Aegis.CountSubarrays.count_subarrays nums1 k = ok r1 →
      Aegis.CountSubarrays.count_subarrays nums2 k = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- If count_subarrays(nums, k) returns r and count_subarrays(nums', k) returns r', then r' >= r.
  Preconditions: Let n = len(nums), and let nums' be the slice of length n + 1 with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = x. Assume 1 <= n <= 99999, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, 1 <= x <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_10 (nums nums' : Slice Std.I64) (x : Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 99999)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hx : 1 ≤ x.val) (hx' : x.val ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (happend : nums'.val = nums.val ++ [x]) :
    ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums' k = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 99999)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hx : 1 ≤ x.val) (hx' : x.val ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (happend : nums'.val = nums.val ++ [x]), ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums' k = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function count_subarrays(nums, k) returns a result r and r = sum_{L=1}^{min(n, q)} (n - L + 1), where q is the greatest integer such that q^2 <= k - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have nums[i] = 1, and 1 <= k <= 1000000000000000. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → elem nums i = 1)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (allOnesCount nums.val.length k.val : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → elem nums i = 1)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∃ r, Aegis.CountSubarrays.count_subarrays nums k = ok r ∧
      r.val = (allOnesCount nums.val.length k.val : Int)) := by
  sorry

/-- If count_subarrays(nums, k) returns r and count_subarrays(nums, k + 1) returns r', then r' - r equals the number of pairs (i, j) such that 0 <= i <= j < n and (sum_{t=i}^{j} nums[t]) * (j - i + 1) = k.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 999999999999999. -/
theorem spec_12 (nums : Slice Std.I64) (k k' : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hksucc : k'.val = k.val + 1) (hk'' : k.val ≤ 999999999999999) :
    ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums k' = ok r' →
      r'.val - r.val = (numEqual (sliceVals nums) k.val : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k k' : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hksucc : k'.val = k.val + 1) (hk'' : k.val ≤ 999999999999999), ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums k' = ok r' →
      r'.val - r.val = (numEqual (sliceVals nums) k.val : Int)) := by
  sorry

/-- If count_subarrays(nums, k) returns r and count_subarrays(rev, k) returns r', then r = r'.
  Preconditions: Let n = len(nums), and let rev be the slice of length n with rev[i] = nums[n - 1 - i] for 0 <= i < n. Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_13 (nums rev : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hrev : rev.val = nums.val.reverse) :
    ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays rev k = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums rev : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (hrev : rev.val = nums.val.reverse), ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays rev k = ok r' → r.val = r'.val) := by
  sorry

/-- If count_subarrays(nums, k) returns r and count_subarrays(nums', k) returns r', then r' = r + #{i | 0 <= i <= n and (sum_{t=i}^{n-1} nums[t] + x) * (n - i + 1) < k}, with the empty sum for i = n taken as 0. This is the exact contribution of the newly appended element.
  Preconditions: Let n = len(nums), and let nums' be the slice of length n + 1 with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = x. Assume 1 <= n <= 99999, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, 1 <= x <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_14 (nums nums' : Slice Std.I64) (x : Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 99999)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hx : 1 ≤ x.val) (hx' : x.val ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (happend : nums'.val = nums.val ++ [x]) :
    ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums' k = ok r' →
      r'.val = r.val + (numNewEndingAt (sliceVals nums) x.val k.val : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (x : Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 99999)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hx : 1 ≤ x.val) (hx' : x.val ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000)
    (happend : nums'.val = nums.val ++ [x]), ∀ r r', Aegis.CountSubarrays.count_subarrays nums k = ok r →
      Aegis.CountSubarrays.count_subarrays nums' k = ok r' →
      r'.val = r.val + (numNewEndingAt (sliceVals nums) x.val k.val : Int)) := by
  sorry

/-- Whenever count_subarrays(nums, k) returns a result r, r = n * (n + 1) / 2 if and only if k > n * total. This gives the exact all-subarrays-qualify threshold, not just the sufficient condition in spec_6.
  Preconditions: Let n = len(nums) and total = sum_{t=0}^{n-1} nums[t]. Assume 1 <= n <= 100000, for every i with 0 <= i < n we have 1 <= nums[i] <= 100000, and 1 <= k <= 1000000000000000. -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000) :
    ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      (r.val = (totalPairs nums.val.length : Int) ↔
        k.val > (nums.val.length : Int) * (sliceVals nums).sum) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : 1 ≤ nums.val.length) (hn' : nums.val.length ≤ 100000)
    (hnum : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100000)
    (hk : 1 ≤ k.val) (hk' : k.val ≤ 1000000000000000), ∀ r, Aegis.CountSubarrays.count_subarrays nums k = ok r →
      (r.val = (totalPairs nums.val.length : Int) ↔
        k.val > (nums.val.length : Int) * (sliceVals nums).sum)) := by
  sorry

end AegisSpec.CountSubarrays
