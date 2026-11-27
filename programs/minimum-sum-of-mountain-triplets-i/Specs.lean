import Aegis.MinimumSum.Code.Funs

/-!
# Specifications of `Aegis.MinimumSum.minimum_sum`

LeetCode problem `minimum-sum-of-mountain-triplets-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumSum (minimum_sum)

set_option autoImplicit false

namespace AegisSpec.MinimumSum

def sv (nums : Slice I64) (t : Nat) : Int := (nums.val[t]!).val

def MountainTriplet (nums : Slice I64) (i j k : Nat) : Prop :=
  i < j ∧ j < k ∧ k < nums.length ∧ sv nums i < sv nums j ∧ sv nums k < sv nums j

def tripletSum (nums : Slice I64) (i j k : Nat) : Int :=
  sv nums i + sv nums j + sv nums k

def HasMountainTriplet (nums : Slice I64) : Prop :=
  ∃ i j k, MountainTriplet nums i j k

def UniqueMountainTriplet (nums : Slice I64) : Prop :=
  ∃ i j k, MountainTriplet nums i j k ∧
    ∀ i' j' k', MountainTriplet nums i' j' k' → i' = i ∧ j' = j ∧ k' = k

/-- Whenever the function returns a result r, the following holds. Call a triple (i,j,k) a mountain triplet if 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j]. If at least one mountain triplet exists, then r != -1, there exists a mountain triplet (i,j,k) with r = nums[i] + nums[j] + nums[k], and for every mountain triplet (i,j,k), r <= nums[i] + nums[j] + nums[k]. If no mountain triplet exists, then r = -1.
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_1 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) :
    (HasMountainTriplet nums →
        r.val ≠ -1 ∧
        (∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k) ∧
        (∀ i j k, MountainTriplet nums i j k → r.val ≤ tripletSum nums i j k)) ∧
      (¬ HasMountainTriplet nums → r.val = -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r), (HasMountainTriplet nums →
        r.val ≠ -1 ∧
        (∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k) ∧
        (∀ i j k, MountainTriplet nums i j k → r.val ≤ tripletSum nums i j k)) ∧
      (¬ HasMountainTriplet nums → r.val = -1)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_2 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50) :
    ∃ r : I64, minimum_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50), ∃ r : I64, minimum_sum nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 4 <= r <= 148.
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_3 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) :
    r.val = -1 ∨ (4 ≤ r.val ∧ r.val ≤ 148) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r), r.val = -1 ∨ (4 ≤ r.val ∧ r.val ≤ 148)) := by
  sorry

/-- Whenever the function returns a result r with r != -1, there exist indices i, j, k such that 0 <= i < j < k < len(nums), nums[i] < nums[j], nums[k] < nums[j], and r = nums[i] + nums[j] + nums[k].
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_4 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) (hne : r.val ≠ -1) :
    ∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) (hne : r.val ≠ -1), ∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k) := by
  sorry

/-- Whenever the function returns a result r with r != -1, for every choice of indices i, j, k with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j], we have r <= nums[i] + nums[j] + nums[k].
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_5 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) (hne : r.val ≠ -1) :
    ∀ i j k, MountainTriplet nums i j k → r.val ≤ tripletSum nums i j k := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) (hne : r.val ≠ -1), ∀ i j k, MountainTriplet nums i j k → r.val ≤ tripletSum nums i j k) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there is no triple of indices (i,j,k) with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j].
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_6 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) :
    (r.val = -1 ↔ ¬ HasMountainTriplet nums) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r), (r.val = -1 ↔ ¬ HasMountainTriplet nums)) := by
  sorry

/-- Whenever the function returns a result r, if nums[0] < nums[1] and nums[2] < nums[1] then r = nums[0] + nums[1] + nums[2], and otherwise r = -1.
  Preconditions: nums is a slice with len(nums) = 3, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_7 (nums : Slice I64)
    (hlen : nums.length = 3)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r) :
    r.val = if sv nums 0 < sv nums 1 ∧ sv nums 2 < sv nums 1
      then sv nums 0 + sv nums 1 + sv nums 2 else -1 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : nums.length = 3)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    {r : I64} (hres : minimum_sum nums = ok r), r.val = if sv nums 0 < sv nums 1 ∧ sv nums 2 < sv nums 1
      then sv nums 0 + sv nums 1 + sv nums 2 else -1) := by
  sorry

/-- Whenever the function returns a result r, r = -1.
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. nums is strictly increasing: for every t with 0 <= t < len(nums) - 1, nums[t] < nums[t+1]. -/
theorem spec_8 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (hinc : ∀ t, t + 1 < nums.length → sv nums t < sv nums (t + 1))
    {r : I64} (hres : minimum_sum nums = ok r) :
    r.val = -1 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (hinc : ∀ t, t + 1 < nums.length → sv nums t < sv nums (t + 1))
    {r : I64} (hres : minimum_sum nums = ok r), r.val = -1) := by
  sorry

/-- Let rev be the slice with len(rev) = len(nums) and rev[t] = nums[len(nums) - 1 - t] for every t with 0 <= t < len(nums). Whenever the function returns a result r on nums and also returns a result r' on rev, r = r'.
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. -/
theorem spec_9 (nums rev : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (hrev_len : rev.length = nums.length)
    (hrev : ∀ t, t < rev.length → sv rev t = sv nums (nums.length - 1 - t))
    {r r' : I64} (hres : minimum_sum nums = ok r) (hres' : minimum_sum rev = ok r') :
    r = r' := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums rev : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (hrev_len : rev.length = nums.length)
    (hrev : ∀ t, t < rev.length → sv rev t = sv nums (nums.length - 1 - t))
    {r r' : I64} (hres : minimum_sum nums = ok r) (hres' : minimum_sum rev = ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, for that unique triple (i,j,k), r = nums[i] + nums[j] + nums[k].
  Preconditions: nums is a slice with 3 <= len(nums) <= 50, and for every t with 0 <= t < len(nums), 1 <= nums[t] <= 50. There is exactly one triple (i,j,k) with 0 <= i < j < k < len(nums), nums[i] < nums[j], and nums[k] < nums[j]. -/
theorem spec_10 (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (huniq : UniqueMountainTriplet nums)
    {r : I64} (hres : minimum_sum nums = ok r) :
    ∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen : 3 ≤ nums.length) (hlen' : nums.length ≤ 50)
    (hbound : ∀ t, t < nums.length → 1 ≤ sv nums t ∧ sv nums t ≤ 50)
    (huniq : UniqueMountainTriplet nums)
    {r : I64} (hres : minimum_sum nums = ok r), ∃ i j k, MountainTriplet nums i j k ∧ r.val = tripletSum nums i j k) := by
  sorry

end AegisSpec.MinimumSum
