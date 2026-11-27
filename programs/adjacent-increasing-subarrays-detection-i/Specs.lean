import Aegis.HasIncreasingSubarrays.Code.Funs

/-!
# Specifications of `Aegis.HasIncreasingSubarrays.has_increasing_subarrays`

LeetCode problem `adjacent-increasing-subarrays-detection-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.HasIncreasingSubarrays

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def InValueRange (nums : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (hi : i < nums.val.length),
    -1000 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000

def StrictlyIncreasing : List ℤ → Prop
  | [] => True
  | [_] => True
  | x :: y :: ys => x < y ∧ StrictlyIncreasing (y :: ys)

def WindowStrictlyIncreasing (xs : List ℤ) (p k : ℕ) : Prop :=
  StrictlyIncreasing ((xs.drop p).take k)

def HasAdjacentIncreasingSubarrays (nums : Slice Std.I64) (k : ℕ) : Prop :=
  ∃ a : ℕ, a + 2 * k ≤ nums.val.length ∧
    WindowStrictlyIncreasing (vals nums) a k ∧
    WindowStrictlyIncreasing (vals nums) (a + k) k

/-- The function returns a Boolean result r (it does not fail), and r = true if and only if there exists an integer a such that 0 <= a, a + 2*k <= len(nums), the subarray nums[a .. a+k-1] is strictly increasing, and the subarray nums[a+k .. a+2*k-1] is strictly increasing. A subarray nums[p .. p+k-1] is strictly increasing when for every i with p <= i < p+k-1, nums[i] < nums[i+1]; for k=1 this condition is vacuously true. Equivalently, the two subarrays start at a and a+k, so they are adjacent.
  Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; k is an integer with 1 <= k and 2*k <= len(nums); and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. All arithmetic and index expressions below are mathematical integers, not machine integers. Subarrays are 0-indexed. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums) :
    ∃ r : Bool,
      Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r ∧
        (r = true ↔ HasAdjacentIncreasingSubarrays nums k.val.toNat) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums), ∃ r : Bool,
      Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r ∧
        (r = true ↔ HasAdjacentIncreasingSubarrays nums k.val.toNat)) := by
  sorry

/-- Let r be the Boolean result returned by has_increasing_subarrays nums k. For every integer k' with 1 <= k' <= k and 2*k' <= len(nums), let r' be the Boolean result returned by has_increasing_subarrays nums k'. Whenever these results are returned, r = true implies r' = true.
  Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; k is an integer with 1 <= k and 2*k <= len(nums); and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. All arithmetic and index expressions below are mathematical integers, not machine integers. Subarrays are 0-indexed. -/
theorem spec_2 (nums : Slice Std.I64) (k k' : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hk'_lb : 1 ≤ k'.val) (hk'_le : k'.val ≤ k.val)
    (hk'_ub : 2 * k'.val ≤ (nums.val.length : ℤ))
    (r r' : Bool)
    (hr : Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r)
    (hr' : Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k' = ok r') :
    r = true → r' = true := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k k' : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hk'_lb : 1 ≤ k'.val) (hk'_le : k'.val ≤ k.val)
    (hk'_ub : 2 * k'.val ≤ (nums.val.length : ℤ))
    (r r' : Bool)
    (hr : Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r)
    (hr' : Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k' = ok r'), r = true → r' = true) := by
  sorry

/-- For every integer c such that -1000 <= nums[i] + c <= 1000 for all i with 0 <= i < len(nums), let nums' be the array of length len(nums) with nums'[i] = nums[i] + c. Then the calls on (nums,k) and (nums',k) both satisfy the problem constraints, and whenever they return Boolean results r and r', we have r = r'.
  Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; k is an integer with 1 <= k and 2*k <= len(nums); and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. All arithmetic and index expressions below are mathematical integers, not machine integers. Subarrays are 0-indexed. -/
theorem spec_3 (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hshift : vals nums' = (vals nums).map (fun v => v + c))
    (hc : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000 ≤ (nums.val[i]'hi).val + c ∧ (nums.val[i]'hi).val + c ≤ 1000) :
    (2 ≤ nums'.val.length ∧ nums'.val.length ≤ 100 ∧ InValueRange nums') ∧
      ∀ r r',
        Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r →
          Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums' k = ok r' →
            r = r' := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64) (c : ℤ)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hlen_eq : nums'.val.length = nums.val.length)
    (hshift : vals nums' = (vals nums).map (fun v => v + c))
    (hc : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000 ≤ (nums.val[i]'hi).val + c ∧ (nums.val[i]'hi).val + c ≤ 1000), (2 ≤ nums'.val.length ∧ nums'.val.length ≤ 100 ∧ InValueRange nums') ∧
      ∀ r r',
        Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok r →
          Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums' k = ok r' →
            r = r') := by
  sorry

/-- Let xs and ys be any slices of integers such that the concatenated slice nums' = xs ++ nums ++ ys has length between 2 and 100 and every entry of nums' is between -1000 and 1000. If the function returns true on (nums,k), then the function returns true on (nums',k).
  Preconditions: len(nums) is an integer with 2 <= len(nums) <= 100; k is an integer with 1 <= k and 2*k <= len(nums); and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. All arithmetic and index expressions below are mathematical integers, not machine integers. Subarrays are 0-indexed. -/
theorem spec_4 (nums nums' xs ys : Slice Std.I64) (k : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hcat : nums'.val = xs.val ++ nums.val ++ ys.val)
    (hlen'_lb : 2 ≤ nums'.val.length) (hlen'_ub : nums'.val.length ≤ 100)
    (hrange' : InValueRange nums') :
    Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok true →
      Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums' k = ok true := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' xs ys : Slice Std.I64) (k : Std.I64)
    (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100)
    (hk_lb : 1 ≤ k.val) (hk_ub : 2 * k.val ≤ (nums.val.length : ℤ))
    (hrange : InValueRange nums)
    (hcat : nums'.val = xs.val ++ nums.val ++ ys.val)
    (hlen'_lb : 2 ≤ nums'.val.length) (hlen'_ub : nums'.val.length ≤ 100)
    (hrange' : InValueRange nums'), Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums k = ok true →
      Aegis.HasIncreasingSubarrays.has_increasing_subarrays nums' k = ok true) := by
  sorry

end AegisSpec.HasIncreasingSubarrays
