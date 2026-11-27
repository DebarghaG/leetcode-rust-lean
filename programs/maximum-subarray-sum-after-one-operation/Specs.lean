import Aegis.MaxSumAfterOperation.Code.Funs

/-!
# Specifications of `Aegis.MaxSumAfterOperation.max_sum_after_operation`

LeetCode problem `maximum-subarray-sum-after-one-operation`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

open Aegis.MaxSumAfterOperation

namespace AegisSpec.MaxSumAfterOperation

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def getI (nums : Slice I64) (j : Nat) : Int := (vals nums).getD j 0

def rangeSum (f : Nat → Int) (l h : Nat) : Int := ((List.range (h + 1)).drop l).map f |>.sum

def b (a : List Int) (i j : Nat) : Int := if j = i then (a.getD i 0) ^ 2 else a.getD j 0

def S (a : List Int) (i l h : Nat) : Int := rangeSum (b a i) l h

def listMax (d : Int) : List Int → Int
  | [] => d
  | x :: xs => xs.foldr max x

def allS (a : List Int) : List Int :=
  (List.range a.length).flatMap fun i =>
    (List.range a.length).flatMap fun l =>
      ((List.range a.length).filter (fun h => l ≤ h)).map fun h => S a i l h

def bestSum (a : List Int) : Int := listMax 0 (allS a)

def allSubSums (a : List Int) : List Int :=
  (List.range a.length).flatMap fun l =>
    ((List.range a.length).filter (fun h => l ≤ h)).map fun h =>
      rangeSum (fun j => a.getD j 0) l h

def maxSubSum (a : List Int) : Int := listMax 0 (allSubSums a)

def maxSq (a : List Int) : Int := listMax 0 ((List.range a.length).map fun i => (a.getD i 0) ^ 2)

def maxGain (a : List Int) : Int :=
  listMax 0 ((List.range a.length).map fun i => (a.getD i 0) ^ 2 - a.getD i 0)

def P (a : List Int) (i : Nat) : Int := ((List.range a.length).map fun j => max 0 (b a i j)).sum

def maxP (a : List Int) : Int := listMax 0 ((List.range a.length).map fun i => P a i)

def total (a : List Int) : Int := a.sum

/-- For every valid nums, the function returns a result res and res is the maximum of all values S(i,l,h) = sum_{j=l}^{h} b(i,j), taken over all integers i,l,h with 0 <= i < len(nums) and 0 <= l <= h < len(nums), where b(i,j) = nums[i]*nums[i] if j=i and b(i,j)=nums[j] otherwise. No subarray is empty, and exactly one index i is squared.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val = bestSum (vals nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val = bestSum (vals nums)) := by
  sorry

/-- For every valid nums, the call max_sum_after_operation nums does not fail: there exists a 64-bit integer res such that max_sum_after_operation nums = Result.ok res. In particular, no out-of-bounds access or arithmetic overflow occurs under the stated constraints.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64, max_sum_after_operation nums = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64, max_sum_after_operation nums = ok res) := by
  sorry

/-- For every valid nums, the function returns a result res and res >= max_{0 <= i < len(nums)} (nums[i]*nums[i]).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64, max_sum_after_operation nums = ok res ∧ maxSq (vals nums) ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64, max_sum_after_operation nums = ok res ∧ maxSq (vals nums) ≤ res.val) := by
  sorry

/-- For every valid nums, the function returns a result res and res >= M0(nums), where M0(nums) is the maximum of sum_{j=l}^{h} nums[j] over all integers l,h with 0 <= l <= h < len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64, max_sum_after_operation nums = ok res ∧ maxSubSum (vals nums) ≤ res.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64, max_sum_after_operation nums = ok res ∧ maxSubSum (vals nums) ≤ res.val) := by
  sorry

/-- For every valid nums, the function returns a result res and res <= M0(nums) + Bmax(nums), where M0(nums) is the maximum non-empty contiguous subarray sum of the original array and Bmax(nums) = max_{0 <= i < len(nums)} (nums[i]*nums[i] - nums[i]).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val ≤ maxSubSum (vals nums) + maxGain (vals nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val ≤ maxSubSum (vals nums) + maxGain (vals nums)) := by
  sorry

/-- For every valid nums, the function returns a result res and res <= max_{0 <= i < len(nums)} P(i), where for each i, b(i,j) = nums[i]*nums[i] if j=i and b(i,j)=nums[j] otherwise, and P(i) = sum_{j=0}^{len(nums)-1} max(0, b(i,j)).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val ≤ maxP (vals nums) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val ≤ maxP (vals nums)) := by
  sorry

/-- For every such nums, the function returns a result res and res = max_{0 <= i < len(nums)} (nums[i]*nums[i]).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 0. -/
theorem spec_7 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 0) :
    ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val = maxSq (vals nums) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 0), ∃ res : I64, max_sum_after_operation nums = ok res ∧ res.val = maxSq (vals nums)) := by
  sorry

/-- For every such nums, the function returns a result res and res = (sum_{j=0}^{len(nums)-1} nums[j]) + max_{0 <= i < len(nums)} (nums[i]*nums[i] - nums[i]).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), 0 <= nums[j] <= 10000. -/
theorem spec_8 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → 0 ≤ getI nums j ∧ getI nums j ≤ 10000) :
    ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val = total (vals nums) + maxGain (vals nums) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → 0 ≤ getI nums j ∧ getI nums j ≤ 10000), ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val = total (vals nums) + maxGain (vals nums)) := by
  sorry

/-- For every such nums, the function returns a result res and res = max(nums[0]*nums[0] + max(0, nums[1]), nums[1]*nums[1] + max(0, nums[0])).
  Preconditions: nums is a slice of 64-bit integers with len(nums)=2 and -10000 <= nums[0], nums[1] <= 10000. -/
theorem spec_9 (nums : Slice I64)
    (h_len : nums.val.length = 2)
    (h_bd0 : -10000 ≤ getI nums 0 ∧ getI nums 0 ≤ 10000)
    (h_bd1 : -10000 ≤ getI nums 1 ∧ getI nums 1 ≤ 10000) :
    ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val = max ((getI nums 0) ^ 2 + max 0 (getI nums 1))
          ((getI nums 1) ^ 2 + max 0 (getI nums 0)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : nums.val.length = 2)
    (h_bd0 : -10000 ≤ getI nums 0 ∧ getI nums 0 ≤ 10000)
    (h_bd1 : -10000 ≤ getI nums 1 ∧ getI nums 1 ≤ 10000), ∃ res : I64,
      max_sum_after_operation nums = ok res ∧
        res.val = max ((getI nums 0) ^ 2 + max 0 (getI nums 1))
          ((getI nums 1) ^ 2 + max 0 (getI nums 0))) := by
  sorry

/-- For every valid nums, let rev be the slice of the same length with rev[k] = nums[len(nums)-1-k] for 0 <= k < len(nums). Then max_sum_after_operation nums and max_sum_after_operation rev both return results res and res', and res = res'.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_10 (nums rev : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000)
    (h_rev : rev.val = nums.val.reverse) :
    ∃ res res' : I64,
      max_sum_after_operation nums = ok res ∧
        max_sum_after_operation rev = ok res' ∧ res.val = res'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums rev : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000)
    (h_rev : rev.val = nums.val.reverse), ∃ res res' : I64,
      max_sum_after_operation nums = ok res ∧
        max_sum_after_operation rev = ok res' ∧ res.val = res'.val) := by
  sorry

/-- For every valid nums, whenever the function returns a result res, there exist integers op, l, h with 0 <= op < len(nums) and 0 <= l <= h < len(nums) such that res = sum_{j=l}^{h} c(j), where c(j)=nums[op]*nums[op] if j=op and c(j)=nums[j] otherwise.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), -10000 <= nums[j] <= 10000. -/
theorem spec_11 (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000)
    (res : I64) (h_res : max_sum_after_operation nums = ok res) :
    ∃ op l h : Nat,
      op < nums.val.length ∧ l ≤ h ∧ h < nums.val.length ∧
        res.val = S (vals nums) op l h := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bd : ∀ j : Nat, j < nums.val.length → -10000 ≤ getI nums j ∧ getI nums j ≤ 10000)
    (res : I64) (h_res : max_sum_after_operation nums = ok res), ∃ op l h : Nat,
      op < nums.val.length ∧ l ≤ h ∧ h < nums.val.length ∧
        res.val = S (vals nums) op l h) := by
  sorry

end AegisSpec.MaxSumAfterOperation
