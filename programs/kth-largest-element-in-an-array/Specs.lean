import Aegis.FindKthLargest.Code.Funs

/-!
# Specifications of `Aegis.FindKthLargest.find_kth_largest`

LeetCode problem `kth-largest-element-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FindKthLargest

namespace AegisSpec.FindKthLargest

def countGt (nums : Slice Std.I64) (r : Std.I64) : ℕ :=
  nums.val.countP fun x => decide (r.val < x.val)

def countGe (nums : Slice Std.I64) (t : Std.I64) : ℕ :=
  nums.val.countP fun x => decide (t.val ≤ x.val)

def countEq (nums : Slice Std.I64) (v : Std.I64) : ℕ :=
  nums.val.countP fun x => decide (x.val = v.val)

def sliceMin (nums : Slice Std.I64) : Option ℤ :=
  (nums.val.map fun x => x.val).min?

def sliceMax (nums : Slice Std.I64) : Option ℤ :=
  (nums.val.map fun x => x.val).max?

def Nonincreasing (sorted : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < sorted.val.length),
    (sorted.val[i + 1]'hi).val ≤ (sorted.val[i]'(by omega)).val

def IsPointwiseNeg (neg nums : Slice Std.I64) : Prop :=
  neg.val.map (fun x => x.val) = nums.val.map (fun x => - x.val)

/-- Whenever find_kth_largest nums k returns Result.ok r, r is the kth largest element of nums counted with multiplicity. Explicitly, let G be the number of indices i with 0 <= i < len(nums) and nums[i] > r, and let E be the number of indices i with 0 <= i < len(nums) and nums[i] >= r. Then G <= k - 1 and E >= k.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      (countGt nums r : ℤ) ≤ k.val - 1 ∧ k.val ≤ (countGe nums r : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      (countGt nums r : ℤ) ≤ k.val - 1 ∧ k.val ≤ (countGe nums r : ℤ)) := by
  sorry

/-- For every input satisfying the preconditions, find_kth_largest nums k returns some Result.ok r; the function does not fail.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∃ r, find_kth_largest nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∃ r, find_kth_largest nums k = ok r) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      ∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, r is between the minimum and maximum entries of nums: min over 0 <= i < len(nums) of nums[i] <= r <= max over 0 <= i < len(nums) of nums[i].
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      ∃ (lo hi : ℤ), sliceMin nums = some lo ∧ sliceMax nums = some hi ∧
        lo ≤ r.val ∧ r.val ≤ hi := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      ∃ (lo hi : ℤ), sliceMin nums = some lo ∧ sliceMax nums = some hi ∧
        lo ≤ r.val ∧ r.val ≤ hi) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, for every slice sorted of length len(nums) that is a permutation of nums (it has the same multiset of values) and is nonincreasing, meaning sorted[0] >= sorted[1] >= ... >= sorted[len(nums)-1], we have sorted[k-1] = r.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      ∀ sorted : Slice Std.I64,
        sorted.val.length = nums.val.length →
        sorted.val.Perm nums.val →
        Nonincreasing sorted →
        sorted.val[k.val.toNat - 1]? = some r := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      ∀ sorted : Slice Std.I64,
        sorted.val.length = nums.val.length →
        sorted.val.Perm nums.val →
        Nonincreasing sorted →
        sorted.val[k.val.toNat - 1]? = some r) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, for every 64-bit integer t, the number of indices i with 0 <= i < len(nums) and nums[i] >= t is at least k if and only if t <= r.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      ∀ t : Std.I64, (k.val ≤ (countGe nums t : ℤ) ↔ t.val ≤ r.val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      ∀ t : Std.I64, (k.val ≤ (countGe nums t : ℤ) ↔ t.val ≤ r.val)) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, r occurs in nums, at least k entries of nums are greater than or equal to r, and for every 64-bit integer v with v > r, fewer than k entries of nums are greater than or equal to v.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      (∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val) ∧
      k.val ≤ (countGe nums r : ℤ) ∧
      (∀ v : Std.I64, r.val < v.val → (countGe nums v : ℤ) < k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      (∃ (i : ℕ) (hi : i < nums.val.length), (nums.val[i]'hi).val = r.val) ∧
      k.val ≤ (countGe nums r : ℤ) ∧
      (∀ v : Std.I64, r.val < v.val → (countGe nums v : ℤ) < k.val)) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r and find_kth_largest ys k returns Result.ok r', we have r = r'.
  Preconditions: 1 <= k <= len(nums) <= 100000, -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums), and ys is a slice of 64-bit integers with len(ys) = len(nums) and the same multiset of values as nums: for every 64-bit integer v, the number of indices i with 0 <= i < len(ys) and ys[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v. -/
theorem spec_8 (nums ys : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000)
    (h_ys_len : ys.val.length = nums.val.length)
    (h_ys_mult : ∀ v : Std.I64, countEq ys v = countEq nums v) :
    ∀ r r', find_kth_largest nums k = ok r → find_kth_largest ys k = ok r' → r = r' := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums ys : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000)
    (h_ys_len : ys.val.length = nums.val.length)
    (h_ys_mult : ∀ v : Std.I64, countEq ys v = countEq nums v), ∀ r r', find_kth_largest nums k = ok r → find_kth_largest ys k = ok r' → r = r') := by
  sorry

/-- Whenever find_kth_largest nums k1 returns Result.ok r1 and find_kth_largest nums k2 returns Result.ok r2, we have r1 >= r2.
  Preconditions: 1 <= k1 <= k2 <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk1_lower : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2_upper : k2.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r1 r2, find_kth_largest nums k1 = ok r1 → find_kth_largest nums k2 = ok r2 →
      r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hk1_lower : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val)
    (hk2_upper : k2.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r1 r2, find_kth_largest nums k1 = ok r1 → find_kth_largest nums k2 = ok r2 →
      r2.val ≤ r1.val) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r and find_kth_largest neg_nums (n - k + 1) returns Result.ok r', we have r' = -r.
  Preconditions: Let n = len(nums). Assume 1 <= k <= n <= 100000 and -10000 <= nums[i] <= 10000 for every i with 0 <= i < n. Let neg_nums be the slice of length n with neg_nums[i] = -nums[i] for every 0 <= i < n. -/
theorem spec_10 (nums neg_nums : Slice Std.I64) (k kneg : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000)
    (h_neg : IsPointwiseNeg neg_nums nums)
    (h_kneg : kneg.val = (nums.val.length : ℤ) - k.val + 1) :
    ∀ r r', find_kth_largest nums k = ok r →
      find_kth_largest neg_nums kneg = ok r' → r'.val = -r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums neg_nums : Slice Std.I64) (k kneg : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000)
    (h_neg : IsPointwiseNeg neg_nums nums)
    (h_kneg : kneg.val = (nums.val.length : ℤ) - k.val + 1), ∀ r r', find_kth_largest nums k = ok r →
      find_kth_largest neg_nums kneg = ok r' → r'.val = -r.val) := by
  sorry

/-- Whenever find_kth_largest nums k returns Result.ok r, let G be the number of indices i with 0 <= i < len(nums) and nums[i] > r, and let C be the number of indices i with 0 <= i < len(nums) and nums[i] = r. Then G <= k - 1 < G + C. In particular, the kth position falls inside the block of entries equal to r after all entries strictly greater than r.
  Preconditions: 1 <= k <= len(nums) <= 100000, and -10000 <= nums[i] <= 10000 for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000) :
    ∀ r, find_kth_largest nums k = ok r →
      (countGt nums r : ℤ) ≤ k.val - 1 ∧
        k.val - 1 < (countGt nums r : ℤ) + (countEq nums r : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hk_lower : 1 ≤ k.val) (hk_upper : k.val ≤ (nums.val.length : ℤ))
    (h_len : (nums.val.length : ℤ) ≤ 100000)
    (h_bound : ∀ (i : ℕ) (hi : i < nums.val.length),
      -10000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 10000), ∀ r, find_kth_largest nums k = ok r →
      (countGt nums r : ℤ) ≤ k.val - 1 ∧
        k.val - 1 < (countGt nums r : ℤ) + (countEq nums r : ℤ)) := by
  sorry

end AegisSpec.FindKthLargest
