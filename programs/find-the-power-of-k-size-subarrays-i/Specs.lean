import Aegis.ResultsArray.Code.Funs

/-!
# Specifications of `Aegis.ResultsArray.results_array`

LeetCode problem `find-the-power-of-k-size-subarrays-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Classical

namespace AegisSpec.ResultsArray

def elem (l : List Std.I64) (i : Nat) : Int := (l.map (fun x => x.val)).getD i 0

/-- Let n = len(nums). The function returns a result res and len(res) = n - k + 1, and for every i with 0 <= i < len(res), res[i] = (if for every j with 0 <= j < k - 1, nums[i+j+1] = nums[i+j] + 1 then nums[i+k-1] else -1).
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_1
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∃ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res ∧
      res.val.length = n - k + 1 ∧
      ∀ i, i < res.val.length →
        elem res.val i =
          (if ∀ j, j < k - 1 → elem nums.val (i + j + 1) = elem nums.val (i + j) + 1
           then elem nums.val (i + k - 1)
           else -1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∃ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res ∧
      res.val.length = n - k + 1 ∧
      ∀ i, i < res.val.length →
        elem res.val i =
          (if ∀ j, j < k - 1 → elem nums.val (i + j + 1) = elem nums.val (i + j) + 1
           then elem nums.val (i + k - 1)
           else -1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, len(res) = n - k + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      res.val.length = n - k + 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      res.val.length = n - k + 1) := by
  sorry

/-- The function returns a result res (it does not fail, panic, overflow, or go out of bounds).
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_3
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∃ res : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums K = Result.ok res := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∃ res : alloc.vec.Vec Std.I64, Aegis.ResultsArray.results_array nums K = Result.ok res) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), either res[i] = -1 or (1 <= res[i] and res[i] <= 100000).
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_4
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 ∨ (1 ≤ elem res.val i ∧ elem res.val i ≤ 100000) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 ∨ (1 ≤ elem res.val i ∧ elem res.val i ≤ 100000)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), res[i] = -1 if and only if there exists j with 0 <= j < k - 1 such that nums[i+j+1] != nums[i+j] + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_5
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        (elem res.val i = -1 ↔
          ∃ j, j < k - 1 ∧ elem nums.val (i + j + 1) ≠ elem nums.val (i + j) + 1) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        (elem res.val i = -1 ↔
          ∃ j, j < k - 1 ∧ elem nums.val (i + j + 1) ≠ elem nums.val (i + j) + 1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), if for every j with 0 <= j < k - 1, nums[i+j+1] = nums[i+j] + 1, then res[i] = nums[i+k-1].
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_6
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        (∀ j, j < k - 1 → elem nums.val (i + j + 1) = elem nums.val (i + j) + 1) →
        elem res.val i = elem nums.val (i + k - 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        (∀ j, j < k - 1 → elem nums.val (i + j + 1) = elem nums.val (i + j) + 1) →
        elem res.val i = elem nums.val (i + k - 1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), if res[i] != -1, then for every j with 0 <= j < k, nums[i+j] <= res[i].
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_7
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        ∀ j, j < k → elem nums.val (i + j) ≤ elem res.val i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        ∀ j, j < k → elem nums.val (i + j) ≤ elem res.val i) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), if res[i] != -1, then res[i] = nums[i] + (k - 1).
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_8
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        elem res.val i = elem nums.val i + ((k : Int) - 1) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        elem res.val i = elem nums.val i + ((k : Int) - 1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), if res[i] != -1, then for every j with 0 <= j < k, nums[i+j] = nums[i] + j.
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_9
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        ∀ j, j < k → elem nums.val (i + j) = elem nums.val i + (j : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i ≠ -1 →
        ∀ j, j < k → elem nums.val (i + j) = elem nums.val i + (j : Int)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, if k = 1, then len(res) = n and for every i with 0 <= i < n, res[i] = nums[i].
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_10
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      k = 1 →
      res.val.length = n ∧ ∀ i, i < n → elem res.val i = elem nums.val i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      k = 1 →
      res.val.length = n ∧ ∀ i, i < n → elem res.val i = elem nums.val i) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, if k = n, then len(res) = 1 and res[0] = (if for every j with 0 <= j < n - 1, nums[j+1] = nums[j] + 1 then nums[n-1] else -1).
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_11
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      k = n →
      res.val.length = 1 ∧
        elem res.val 0 =
          (if ∀ j, j < n - 1 → elem nums.val (j + 1) = elem nums.val j + 1
           then elem nums.val (n - 1)
           else -1) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      k = n →
      res.val.length = 1 ∧
        elem res.val 0 =
          (if ∀ j, j < n - 1 → elem nums.val (j + 1) = elem nums.val j + 1
           then elem nums.val (n - 1)
           else -1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, if k >= 2 and there exists c such that for every i with 0 <= i < n, nums[i] = c, then len(res) = n - k + 1 and for every i with 0 <= i < len(res), res[i] = -1.
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_12
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      2 ≤ k →
      (∃ c : Int, ∀ i, i < n → elem nums.val i = c) →
      res.val.length = n - k + 1 ∧ ∀ i, i < res.val.length → elem res.val i = -1 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      2 ≤ k →
      (∃ c : Int, ∀ i, i < n → elem nums.val i = c) →
      res.val.length = n - k + 1 ∧ ∀ i, i < res.val.length → elem res.val i = -1) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, if for every i with 0 <= i < n - 1, nums[i+1] = nums[i] + 1, then for every i with 0 <= i < len(res), res[i] = nums[i+k-1].
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_13
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      (∀ i, i < n - 1 → elem nums.val (i + 1) = elem nums.val i + 1) →
      ∀ i, i < res.val.length → elem res.val i = elem nums.val (i + k - 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      (∀ i, i < n - 1 → elem nums.val (i + 1) = elem nums.val i + 1) →
      ∀ i, i < res.val.length → elem res.val i = elem nums.val (i + k - 1)) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), if res[i] = -1, then there exists j with 0 <= j < k - 1 such that nums[i+j+1] != nums[i+j] + 1.
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_14
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 →
        ∃ j, j < k - 1 ∧ elem nums.val (i + j + 1) ≠ elem nums.val (i + j) + 1 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 →
        ∃ j, j < k - 1 ∧ elem nums.val (i + j + 1) ≠ elem nums.val (i + j) + 1) := by
  sorry

/-- Let n = len(nums). Whenever the function returns a result res, for every i with 0 <= i < len(res), res[i] = -1 or res[i] = nums[i+k-1].
  Preconditions: Let n = len(nums). 1 <= n <= 500, 1 <= k <= n, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_15
    (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000) :
    ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 ∨ elem res.val i = elem nums.val (i + k - 1) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (K : Std.I64) (n k : Nat)
    (hn : n = nums.val.length) (hval_k : K.val = (k : Int))
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 500)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (hrange : ∀ i, i < n → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 100000), ∀ res : alloc.vec.Vec Std.I64,
      Aegis.ResultsArray.results_array nums K = Result.ok res →
      ∀ i, i < res.val.length →
        elem res.val i = -1 ∨ elem res.val i = elem nums.val (i + k - 1)) := by
  sorry

end AegisSpec.ResultsArray
