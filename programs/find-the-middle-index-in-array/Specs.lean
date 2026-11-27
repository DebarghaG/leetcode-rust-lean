import Aegis.FindMiddleIndex.Code.Funs

/-!
# Specifications of `Aegis.FindMiddleIndex.find_middle_index`

LeetCode problem `find-the-middle-index-in-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMiddleIndex

def vals (nums : Aeneas.Std.Slice Aeneas.Std.I64) : List Int :=
  nums.val.map (fun x => x.val)

def entry (nums : Aeneas.Std.Slice Aeneas.Std.I64) (i : Nat) : Int := (nums.val[i]!).val

def inBounds (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Prop :=
  ∀ i : Nat, i < nums.val.length → -1000 ≤ entry nums i ∧ entry nums i ≤ 1000

def L (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Nat) : Int := ((vals nums).take k).sum

def R (nums : Aeneas.Std.Slice Aeneas.Std.I64) (k : Nat) : Int :=
  ((vals nums).drop (k + 1)).sum

def total (nums : Aeneas.Std.Slice Aeneas.Std.I64) : Int := (vals nums).sum

def ridx (r : Aeneas.Std.I64) : Nat := r.val.toNat

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). The function returns a result r and exactly one of the following holds: (a) r = -1 and for every k with 0 <= k < n, L(k) != R(k); (b) 0 <= r < n, L(r) = R(r), and for every k with 0 <= k < r, L(k) != R(k).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_1 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∃ r : Aeneas.Std.I64,
      Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧
        ((r.val = -1 ∧ ∀ k : Nat, k < nums.val.length → L nums k ≠ R nums k) ∨
         (0 ≤ r.val ∧ r.val < (nums.val.length : Int) ∧
          L nums (ridx r) = R nums (ridx r) ∧
          ∀ k : Nat, k < ridx r → L nums k ≠ R nums k)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∃ r : Aeneas.Std.I64,
      Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧
        ((r.val = -1 ∧ ∀ k : Nat, k < nums.val.length → L nums k ≠ R nums k) ∨
         (0 ≤ r.val ∧ r.val < (nums.val.length : Int) ∧
          L nums (ridx r) = R nums (ridx r) ∧
          ∀ k : Nat, k < ridx r → L nums k ≠ R nums k))) := by
  sorry

/-- The function returns a result r (i.e., it does not fail).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_2 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result r, either r = -1 or (0 <= r and r < n).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_3 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int))) := by
  sorry

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). Whenever the function returns a result r with r != -1, L(r) = R(r).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_4 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → L nums (ridx r) = R nums (ridx r) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → L nums (ridx r) = R nums (ridx r)) := by
  sorry

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). Whenever the function returns a result r with r != -1, for every k with 0 <= k < r, L(k) != R(k).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_5 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → ∀ k : Nat, k < ridx r → L nums k ≠ R nums k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → ∀ k : Nat, k < ridx r → L nums k ≠ R nums k) := by
  sorry

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). The function returns -1 if and only if for every k with 0 <= k < n, L(k) != R(k).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_6 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    (∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = -1) ↔
      ∀ k : Nat, k < nums.val.length → L nums k ≠ R nums k := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), (∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = -1) ↔
      ∀ k : Nat, k < nums.val.length → L nums k ≠ R nums k) := by
  sorry

/-- If len(nums) = 1, then the function returns 0.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_7 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hlen : nums.val.length = 1) :
    ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hlen : nums.val.length = 1), ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0) := by
  sorry

/-- If for every i with 0 <= i < len(nums), nums[i] = 0, then the function returns 0.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_8 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums)
    (hzero : ∀ i : Nat, i < nums.val.length → entry nums i = 0) :
    ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums)
    (hzero : ∀ i : Nat, i < nums.val.length → entry nums i = 0), ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0) := by
  sorry

/-- Let n = len(nums). If the sum of nums[i] for 1 <= i < n equals 0 (with empty sum 0 when n=1), then the function returns 0.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_9 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hsum : ((vals nums).drop 1).sum = 0) :
    ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hsum : ((vals nums).drop 1).sum = 0), ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0) := by
  sorry

/-- Let n = len(nums) and total = sum of nums[i] for 0 <= i < n. For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0). Whenever the function returns a result r with r != -1, total = nums[r] + 2 * L(r).
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_10 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → total nums = entry nums (ridx r) + 2 * L nums (ridx r) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∀ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r →
      r.val ≠ -1 → total nums = entry nums (ridx r) + 2 * L nums (ridx r)) := by
  sorry

/-- If len(nums) = 2, let a = nums[0] and b = nums[1]. Then: if b = 0, the function returns 0; if b != 0 and a = 0, the function returns 1; if a != 0 and b != 0, the function returns -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_11 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hlen : nums.val.length = 2) :
    (entry nums 1 = 0 →
        ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0) ∧
      (entry nums 1 ≠ 0 → entry nums 0 = 0 →
        ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 1) ∧
      (entry nums 0 ≠ 0 → entry nums 1 ≠ 0 →
        ∃ r : Aeneas.Std.I64,
          Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) (hlen : nums.val.length = 2), (entry nums 1 = 0 →
        ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 0) ∧
      (entry nums 1 ≠ 0 → entry nums 0 = 0 →
        ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = 1) ∧
      (entry nums 0 ≠ 0 → entry nums 1 ≠ 0 →
        ∃ r : Aeneas.Std.I64,
          Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = -1)) := by
  sorry

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). If there exists k with 0 <= k < n and L(k) = R(k), then the function returns a result r with r != -1.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_12 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums)
    (hex : ∃ k : Nat, k < nums.val.length ∧ L nums k = R nums k) :
    ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val ≠ -1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums)
    (hex : ∃ k : Nat, k < nums.val.length ∧ L nums k = R nums k), ∃ r : Aeneas.Std.I64, Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val ≠ -1) := by
  sorry

/-- Let n = len(nums). For 0 <= k < n, let L(k) = sum of nums[i] for 0 <= i < k (empty sum 0) and R(k) = sum of nums[i] for k < i < n (empty sum 0). If there is exactly one k with 0 <= k < n and L(k) = R(k), then the function returns that k.
  Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), -1000 <= nums[i] <= 1000. -/
theorem spec_13 (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums) :
    ∀ k : Nat, k < nums.val.length → L nums k = R nums k →
      (∀ j : Nat, j < nums.val.length → L nums j = R nums j → j = k) →
        ∃ r : Aeneas.Std.I64,
          Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = (k : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Aeneas.Std.Slice Aeneas.Std.I64)
    (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100)
    (hbound : inBounds nums), ∀ k : Nat, k < nums.val.length → L nums k = R nums k →
      (∀ j : Nat, j < nums.val.length → L nums j = R nums j → j = k) →
        ∃ r : Aeneas.Std.I64,
          Aegis.FindMiddleIndex.find_middle_index nums = ok r ∧ r.val = (k : Int)) := by
  sorry

end AegisSpec.FindMiddleIndex
