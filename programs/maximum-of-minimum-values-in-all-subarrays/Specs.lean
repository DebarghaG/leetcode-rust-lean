import Aegis.FindMaximums.Code.Funs

/-!
# Specifications of `Aegis.FindMaximums.find_maximums`

LeetCode problem `maximum-of-minimum-values-in-all-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.FindMaximums

  namespace AegisSpec.FindMaximums

  def contents (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

  def outContents (ans : alloc.vec.Vec Std.I64) : List Int :=
    ans.val.map (fun x => x.val)

  def listMin : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl min x

  def listMax : List Int → Int
    | [] => 0
    | x :: xs => xs.foldl max x

  def windowMin (a : List Int) (j len : Nat) : Int :=
    listMin ((List.range len).map (fun k => a[j + k]!))

  def windowMax (a : List Int) (count len : Nat) : Int :=
    listMax ((List.range count).map (fun j => windowMin a j len))

  /-- Whenever find_maximums(nums) returns a result ans, it satisfies len(ans) = n and, for every i with 0 <= i < n, ans[i] = max { min { nums[j+k] | 0 <= k <= i } | 0 <= j <= n-1-i }. Here the inner min is the minimum of the contiguous subarray nums[j], nums[j+1], ..., nums[j+i], and the outer max is over all contiguous subarrays of nums of length i+1.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length ∧
        ∀ i, i < (contents nums).length →
          (outContents ans)[i]! =
            windowMax (contents nums) ((contents nums).length - i) (i + 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length ∧
          ∀ i, i < (contents nums).length →
            (outContents ans)[i]! =
              windowMax (contents nums) ((contents nums).length - i) (i + 1)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans, len(ans) = n.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length) := by
    sorry

  /-- find_maximums(nums) returns a result ans; it does not fail.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∃ ans, find_maximums nums = ok ans := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∃ ans, find_maximums nums = ok ans) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n, min_{0 <= k < n} nums[k] <= ans[i] <= max_{0 <= k < n} nums[k].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          listMin (contents nums) ≤ (outContents ans)[i]! ∧
            (outContents ans)[i]! ≤ listMax (contents nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            listMin (contents nums) ≤ (outContents ans)[i]! ∧
              (outContents ans)[i]! ≤ listMax (contents nums)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n and every j with 0 <= j <= n-1-i, min_{0 <= k <= i} nums[j+k] <= ans[i].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          ∀ j, j ≤ (contents nums).length - 1 - i →
            windowMin (contents nums) j (i + 1) ≤ (outContents ans)[i]! := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            ∀ j, j ≤ (contents nums).length - 1 - i →
              windowMin (contents nums) j (i + 1) ≤ (outContents ans)[i]!) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n, there exists j with 0 <= j <= n-1-i such that ans[i] = min_{0 <= k <= i} nums[j+k].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          ∃ j, j ≤ (contents nums).length - 1 - i ∧
            (outContents ans)[i]! = windowMin (contents nums) j (i + 1) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            ∃ j, j ≤ (contents nums).length - 1 - i ∧
              (outContents ans)[i]! = windowMin (contents nums) j (i + 1)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, ans[0] = max_{0 <= k < n} nums[k].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        (outContents ans)[0]! = listMax (contents nums) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          (outContents ans)[0]! = listMax (contents nums)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, ans[n-1] = min_{0 <= k < n} nums[k].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        (outContents ans)[(contents nums).length - 1]! = listMin (contents nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          (outContents ans)[(contents nums).length - 1]! = listMin (contents nums)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i and j with 0 <= i <= j < n, ans[i] >= ans[j].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, ∀ j, i ≤ j → j < (contents nums).length →
          (outContents ans)[i]! ≥ (outContents ans)[j]! := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, ∀ j, i ≤ j → j < (contents nums).length →
            (outContents ans)[i]! ≥ (outContents ans)[j]!) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n, there exists k with 0 <= k < n such that ans[i] = nums[k].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          ∃ k, k < (contents nums).length ∧ (outContents ans)[i]! = (contents nums)[k]! := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            ∃ k, k < (contents nums).length ∧ (outContents ans)[i]! = (contents nums)[k]!) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n and every integer t, ans[i] >= t if and only if there exists j with 0 <= j <= n-1-i such that for every k with 0 <= k <= i, nums[j+k] >= t.
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          ∀ t : Int,
            ((outContents ans)[i]! ≥ t ↔
              ∃ j, j ≤ (contents nums).length - 1 - i ∧
                ∀ k, k ≤ i → (contents nums)[j + k]! ≥ t) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            ∀ t : Int,
              ((outContents ans)[i]! ≥ t ↔
                ∃ j, j ≤ (contents nums).length - 1 - i ∧
                  ∀ k, k ≤ i → (contents nums)[j + k]! ≥ t)) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n, ans[i] = nums[n-1-i].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. Additionally, nums is nondecreasing: nums[k] <= nums[k+1] for every k with 0 <= k < n-1. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000)
      (hn_mono : ∀ k, k < (contents nums).length - 1 →
        (contents nums)[k]! ≤ (contents nums)[k + 1]!) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          (outContents ans)[i]! = (contents nums)[(contents nums).length - 1 - i]! := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000)
        (hn_mono : ∀ k, k < (contents nums).length - 1 →
          (contents nums)[k]! ≤ (contents nums)[k + 1]!), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            (outContents ans)[i]! = (contents nums)[(contents nums).length - 1 - i]!) := by
    sorry

  /-- Whenever find_maximums(nums) returns a result ans with len(ans) = n, for every i with 0 <= i < n, ans[i] = nums[i].
    Preconditions: Let n = len(nums). The slice satisfies n >= 1, n <= 100000, and 0 <= nums[k] <= 1000000000 for every k with 0 <= k < n. Additionally, nums is nonincreasing: nums[k] >= nums[k+1] for every k with 0 <= k < n-1. -/
  theorem spec_13 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ (contents nums).length)
      (hn_le : (contents nums).length ≤ 100000)
      (hn_bounds : ∀ k, k < (contents nums).length →
        0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000)
      (hn_anti : ∀ k, k < (contents nums).length - 1 →
        (contents nums)[k]! ≥ (contents nums)[k + 1]!) :
      ∀ ans, find_maximums nums = ok ans →
        (outContents ans).length = (contents nums).length →
        ∀ i, i < (contents nums).length →
          (outContents ans)[i]! = (contents nums)[i]! := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ (contents nums).length)
        (hn_le : (contents nums).length ≤ 100000)
        (hn_bounds : ∀ k, k < (contents nums).length →
          0 ≤ (contents nums)[k]! ∧ (contents nums)[k]! ≤ 1000000000)
        (hn_anti : ∀ k, k < (contents nums).length - 1 →
          (contents nums)[k]! ≥ (contents nums)[k + 1]!), ∀ ans, find_maximums nums = ok ans →
          (outContents ans).length = (contents nums).length →
          ∀ i, i < (contents nums).length →
            (outContents ans)[i]! = (contents nums)[i]!) := by
    sorry

  end AegisSpec.FindMaximums
