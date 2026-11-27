import Aegis.LongestSquareStreak.Code.Funs

/-!
# Specifications of `Aegis.LongestSquareStreak.longest_square_streak`

LeetCode problem `longest-square-streak-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.LongestSquareStreak

namespace AegisSpec.LongestSquareStreak

def elem (nums : Slice Std.I64) (i : Nat) : Int :=
  match nums.val[i]? with
  | some v => v.val
  | none => 0

def Occurs (nums : Slice Std.I64) (x : Int) : Prop :=
  ∃ i : Nat, i < nums.val.length ∧ elem nums i = x

def InRange (nums : Slice Std.I64) : Prop :=
  ∀ i : Nat, i < nums.val.length → 2 ≤ elem nums i ∧ elem nums i ≤ 100000

def SquareStreak (nums : Slice Std.I64) (L : Nat) : Prop :=
  ∃ x : Nat → Int,
    (∀ t : Nat, t < L → Occurs nums (x t)) ∧
    (∀ t : Nat, t + 1 < L → x (t + 1) = x t * x t)

/-- Whenever the function returns a result r, r is determined as follows. Define a square streak of length L in nums, for L >= 2, to mean that there exist integers x_0, ..., x_{L-1} such that each x_t occurs in nums (there is an index i with nums[i] = x_t) and x_t = x_{t-1} * x_{t-1} for every t with 1 <= t < L. If no L >= 2 admits a square streak of length L in nums, then r = -1. Otherwise r is the largest L >= 2 such that nums contains a square streak of length L; equivalently, if r >= 2 then nums contains a square streak of length r and every square streak in nums has length at most r.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) :
    (r.val = -1 ∧ ∀ L : Nat, 2 ≤ L → ¬ SquareStreak nums L) ∨
      (2 ≤ r.val ∧ SquareStreak nums r.val.toNat ∧
        ∀ L : Nat, 2 ≤ L → SquareStreak nums L → (L : Int) ≤ r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r), (r.val = -1 ∧ ∀ L : Nat, 2 ≤ L → ¬ SquareStreak nums L) ∨
      (2 ≤ r.val ∧ SquareStreak nums r.val.toNat ∧
        ∀ L : Nat, 2 ≤ L → SquareStreak nums L → (L : Int) ≤ r.val)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums) :
    ∃ r : Std.I64, longest_square_streak nums = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums), ∃ r : Std.I64, longest_square_streak nums = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, either r = -1 or 2 <= r <= 5.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) :
    r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ 5) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r), r.val = -1 ∨ (2 ≤ r.val ∧ r.val ≤ 5)) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, we have r <= len(nums).
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val) :
    r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val), r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, there exist integers x_0, ..., x_{r-1} such that each x_t occurs in nums and x_t = x_{t-1} * x_{t-1} for every t with 1 <= t < r; that is, nums contains a square streak of length r.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val) :
    SquareStreak nums r.val.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val), SquareStreak nums r.val.toNat) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, every square streak in nums has length at most r. Here a square streak of length L in nums, for L >= 2, means there exist x_0, ..., x_{L-1}, each occurring in nums, with x_t = x_{t-1} * x_{t-1} for every t with 1 <= t < L.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val) :
    ∀ L : Nat, 2 ≤ L → SquareStreak nums L → (L : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val), ∀ L : Nat, 2 ≤ L → SquareStreak nums L → (L : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = -1 if and only if there do not exist two distinct indices i and j with 0 <= i < len(nums), 0 <= j < len(nums), and nums[j] = nums[i] * nums[i].
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) :
    (r.val = -1 ↔
      ¬ (∃ i j : Nat, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
          elem nums j = elem nums i * elem nums i)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r), (r.val = -1 ↔
      ¬ (∃ i j : Nat, i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧
          elem nums j = elem nums i * elem nums i))) := by
  sorry

/-- Whenever the function returns a result r with r >= 2, for every L with 2 <= L <= r, nums contains a square streak of length L (values x_0, ..., x_{L-1} occurring in nums with x_t = x_{t-1} * x_{t-1} for 1 <= t < L).
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_8 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val) :
    ∀ L : Nat, 2 ≤ L → (L : Int) ≤ r.val → SquareStreak nums L := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) (hr : 2 ≤ r.val), ∀ L : Nat, 2 ≤ L → (L : Int) ≤ r.val → SquareStreak nums L) := by
  sorry

/-- Whenever the function returns a result r, r = 5 if and only if the five values 2, 4, 16, 256, and 65536 each occur in nums.
  Preconditions: len(nums) >= 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_9 (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) :
    (r.val = 5 ↔
      (Occurs nums 2 ∧ Occurs nums 4 ∧ Occurs nums 16 ∧ Occurs nums 256 ∧
        Occurs nums 65536)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : 2 ≤ nums.val.length) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r), (r.val = 5 ↔
      (Occurs nums 2 ∧ Occurs nums 4 ∧ Occurs nums 16 ∧ Occurs nums 256 ∧
        Occurs nums 65536))) := by
  sorry

/-- Whenever the function returns a result r, r = 2 if nums[0] * nums[0] = nums[1] or nums[1] * nums[1] = nums[0]; otherwise r = -1.
  Preconditions: len(nums) = 2; for every i with 0 <= i < len(nums), 2 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (hlen : nums.val.length = 2) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r) :
    ((elem nums 0 * elem nums 0 = elem nums 1 ∨ elem nums 1 * elem nums 1 = elem nums 0) ∧
        r.val = 2) ∨
      (¬ (elem nums 0 * elem nums 0 = elem nums 1 ∨ elem nums 1 * elem nums 1 = elem nums 0) ∧
        r.val = -1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen : nums.val.length = 2) (hrange : InRange nums)
    (r : Std.I64) (hres : longest_square_streak nums = Result.ok r), ((elem nums 0 * elem nums 0 = elem nums 1 ∨ elem nums 1 * elem nums 1 = elem nums 0) ∧
        r.val = 2) ∨
      (¬ (elem nums 0 * elem nums 0 = elem nums 1 ∨ elem nums 1 * elem nums 1 = elem nums 0) ∧
        r.val = -1)) := by
  sorry

/-- For any two such arrays nums1 and nums2, if for every integer v, v occurs in nums1 if and only if v occurs in nums2, then whenever the function returns r1 on nums1 and r2 on nums2, we have r1 = r2.
  Preconditions: nums1 and nums2 each satisfy len >= 2; for every i with 0 <= i < len(nums1), 2 <= nums1[i] <= 100000; for every i with 0 <= i < len(nums2), 2 <= nums2[i] <= 100000. -/
theorem spec_11 (nums1 nums2 : Slice Std.I64)
    (hlen1 : 2 ≤ nums1.val.length) (hrange1 : InRange nums1)
    (hlen2 : 2 ≤ nums2.val.length) (hrange2 : InRange nums2)
    (hsame : ∀ v : Int, Occurs nums1 v ↔ Occurs nums2 v)
    (r1 r2 : Std.I64) (hres1 : longest_square_streak nums1 = Result.ok r1)
    (hres2 : longest_square_streak nums2 = Result.ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen1 : 2 ≤ nums1.val.length) (hrange1 : InRange nums1)
    (hlen2 : 2 ≤ nums2.val.length) (hrange2 : InRange nums2)
    (hsame : ∀ v : Int, Occurs nums1 v ↔ Occurs nums2 v)
    (r1 r2 : Std.I64) (hres1 : longest_square_streak nums1 = Result.ok r1)
    (hres2 : longest_square_streak nums2 = Result.ok r2), r1.val = r2.val) := by
  sorry

/-- For any two such arrays nums1 and nums2, if every value that occurs in nums1 also occurs in nums2, then whenever the function returns r1 on nums1 and r2 on nums2, either r1 = -1 or (r2 >= 2 and r2 >= r1).
  Preconditions: nums1 and nums2 each satisfy len >= 2; for every i with 0 <= i < len(nums1), 2 <= nums1[i] <= 100000; for every i with 0 <= i < len(nums2), 2 <= nums2[i] <= 100000. -/
theorem spec_12 (nums1 nums2 : Slice Std.I64)
    (hlen1 : 2 ≤ nums1.val.length) (hrange1 : InRange nums1)
    (hlen2 : 2 ≤ nums2.val.length) (hrange2 : InRange nums2)
    (hsub : ∀ v : Int, Occurs nums1 v → Occurs nums2 v)
    (r1 r2 : Std.I64) (hres1 : longest_square_streak nums1 = Result.ok r1)
    (hres2 : longest_square_streak nums2 = Result.ok r2) :
    r1.val = -1 ∨ (2 ≤ r2.val ∧ r1.val ≤ r2.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64)
    (hlen1 : 2 ≤ nums1.val.length) (hrange1 : InRange nums1)
    (hlen2 : 2 ≤ nums2.val.length) (hrange2 : InRange nums2)
    (hsub : ∀ v : Int, Occurs nums1 v → Occurs nums2 v)
    (r1 r2 : Std.I64) (hres1 : longest_square_streak nums1 = Result.ok r1)
    (hres2 : longest_square_streak nums2 = Result.ok r2), r1.val = -1 ∨ (2 ≤ r2.val ∧ r1.val ≤ r2.val)) := by
  sorry

end AegisSpec.LongestSquareStreak
