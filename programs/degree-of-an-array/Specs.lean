import Aegis.FindShortestSubArray.Code.Funs

/-!
# Specifications of `Aegis.FindShortestSubArray.find_shortest_sub_array`

LeetCode problem `degree-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindShortestSubArray

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (vals nums).getD i 0

def subarray (nums : Slice Std.I64) (l h : ℕ) : List ℤ :=
  ((vals nums).drop l).take (h - l)

def freq (nums : Slice Std.I64) (l h : ℕ) (v : ℤ) : ℕ :=
  (subarray nums l h).countP (fun x => decide (x = v))

def degree (nums : Slice Std.I64) (l h : ℕ) : ℕ :=
  (subarray nums l h).foldr (fun x m => max (freq nums l h x) m) 0

def degreeAll (nums : Slice Std.I64) : ℕ := degree nums 0 (vals nums).length

def occurs (nums : Slice Std.I64) (v : ℤ) : Prop := v ∈ vals nums

def firstOcc (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  ((List.range (vals nums).length).find? (fun i => decide (elem nums i = v))).getD 0

def lastOcc (nums : Slice Std.I64) (v : ℤ) : ℕ :=
  ((List.range (vals nums).length).reverse.find? (fun i => decide (elem nums i = v))).getD 0

/-- Whenever find_shortest_sub_array(nums) returns a result r, the integer r equals the minimum of h-l over all pairs (l,h) with 0 <= l < h <= n and degree(l,h) = D. The minimum is over a nonempty set because the whole array (0,n) has degree(0,n) = D.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h) (equivalently, the maximum over i with l <= i < h of freq(l,h,nums[i])). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. The notation nums[l..h) denotes the contiguous subarray with indices l, l+1, ..., h-1. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (∃ l h, l < h ∧ h ≤ nums.val.length ∧ degree nums l h = degreeAll nums ∧
        r.val = (h : ℤ) - (l : ℤ)) ∧
      (∀ l h, l < h → h ≤ nums.val.length → degree nums l h = degreeAll nums →
        r.val ≤ (h : ℤ) - (l : ℤ)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (∃ l h, l < h ∧ h ≤ nums.val.length ∧ degree nums l h = degreeAll nums ∧
        r.val = (h : ℤ) - (l : ℤ)) ∧
      (∀ l h, l < h → h ≤ nums.val.length → degree nums l h = degreeAll nums →
        r.val ≤ (h : ℤ) - (l : ℤ))) := by
  sorry

/-- find_shortest_sub_array(nums) returns a result r; equivalently, on every input satisfying the preconditions the function does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∃ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∃ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, 1 <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, r <= n = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val ≤ (nums.val.length : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val ≤ (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, r >= D.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (degreeAll nums : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (degreeAll nums : ℤ) ≤ r.val) := by
  sorry

/-- If n = 1, then whenever find_shortest_sub_array(nums) returns a result r, r = 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_one : nums.val.length = 1) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r → r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_one : nums.val.length = 1), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r → r.val = 1) := by
  sorry

/-- If nums[i] = nums[0] for every i with 0 <= i < n, then whenever find_shortest_sub_array(nums) returns a result r, r = n.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). -/
theorem spec_7 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_const : ∀ i, i < nums.val.length → elem nums i = elem nums 0) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_const : ∀ i, i < nums.val.length → elem nums i = elem nums 0), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val = (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, r = 1 if and only if D = 1, which is equivalent to: for all i,j with 0 <= i < j < n, nums[i] != nums[j].
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). -/
theorem spec_8 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (r.val = 1 ↔ degreeAll nums = 1) ∧
      (degreeAll nums = 1 ↔
        ∀ i j, i < j → j < nums.val.length → elem nums i ≠ elem nums j) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (r.val = 1 ↔ degreeAll nums = 1) ∧
      (degreeAll nums = 1 ↔
        ∀ i j, i < j → j < nums.val.length → elem nums i ≠ elem nums j)) := by
  sorry

/-- If n >= 2 and nums[0] != nums[n-1], then whenever find_shortest_sub_array(nums) returns a result r, r < n.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_two : 2 ≤ nums.val.length)
    (h_ends : elem nums 0 ≠ elem nums (nums.val.length - 1)) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val < (nums.val.length : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_two : 2 ≤ nums.val.length)
    (h_ends : elem nums 0 ≠ elem nums (nums.val.length - 1)), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      r.val < (nums.val.length : ℤ)) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, for every value v occurring in nums with freq(0,n,v) = D, we have r <= last(v) - first(v) + 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. -/
theorem spec_10 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val ≤ (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val ≤ (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, there exists a value v occurring in nums such that freq(0,n,v) = D and r = last(v) - first(v) + 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. -/
theorem spec_11 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∃ v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums ∧
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∃ v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums ∧
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, for every pair (l,h) with 0 <= l < h <= n and h-l < r, we have degree(l,h) != D.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). -/
theorem spec_12 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ l h, l < h → h ≤ nums.val.length → (h : ℤ) - (l : ℤ) < r.val →
        degree nums l h ≠ degreeAll nums := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ l h, l < h → h ≤ nums.val.length → (h : ℤ) - (l : ℤ) < r.val →
        degree nums l h ≠ degreeAll nums) := by
  sorry

/-- Let rev(nums) be the slice of length n defined by rev(nums)[i] = nums[n-1-i] for 0 <= i < n. Whenever find_shortest_sub_array(nums) returns r and find_shortest_sub_array(rev(nums)) returns r', we have r = r'.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). -/
theorem spec_13 (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_rev : vals nums' = (vals nums).reverse) :
    ∀ r r', Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      Aegis.FindShortestSubArray.find_shortest_sub_array nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_rev : vals nums' = (vals nums).reverse), ∀ r r', Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      Aegis.FindShortestSubArray.find_shortest_sub_array nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Let V be the set of values occurring in nums. Let g be any function that is injective on V and satisfies 0 <= g(v) <= 49999 for every v in V, and let nums' be any slice of length n with nums'[i] = g(nums[i]) for all i with 0 <= i < n. Whenever find_shortest_sub_array(nums) returns r and find_shortest_sub_array(nums') returns r', we have r = r'.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). -/
theorem spec_14 (nums nums' : Slice Std.I64) (g : ℤ → ℤ)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_inj : ∀ v w, occurs nums v → occurs nums w → g v = g w → v = w)
    (h_g_range : ∀ v, occurs nums v → 0 ≤ g v ∧ g v ≤ 49999)
    (h_len' : nums'.val.length = nums.val.length)
    (h_map : ∀ i, i < nums.val.length → elem nums' i = g (elem nums i)) :
    ∀ r r', Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      Aegis.FindShortestSubArray.find_shortest_sub_array nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (g : ℤ → ℤ)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_inj : ∀ v w, occurs nums v → occurs nums w → g v = g w → v = w)
    (h_g_range : ∀ v, occurs nums v → 0 ≤ g v ∧ g v ≤ 49999)
    (h_len' : nums'.val.length = nums.val.length)
    (h_map : ∀ i, i < nums.val.length → elem nums' i = g (elem nums i)), ∀ r r', Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      Aegis.FindShortestSubArray.find_shortest_sub_array nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, there exist indices l,h with 0 <= l < h <= n such that h-l = r and degree(l,h) = D.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). -/
theorem spec_15 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∃ l h, l < h ∧ h ≤ nums.val.length ∧ r.val = (h : ℤ) - (l : ℤ) ∧
        degree nums l h = degreeAll nums := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∃ l h, l < h ∧ h ≤ nums.val.length ∧ r.val = (h : ℤ) - (l : ℤ) ∧
        degree nums l h = degreeAll nums) := by
  sorry

/-- If there is exactly one value v occurring in nums with freq(0,n,v) = D, then whenever find_shortest_sub_array(nums) returns a result r, r = last(v) - first(v) + 1.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. -/
theorem spec_16 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_unique : ∃! v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1 := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999)
    (h_unique : ∃! v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      ∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) := by
  sorry

/-- Whenever find_shortest_sub_array(nums) returns a result r, r = min { last(v) - first(v) + 1 | v occurs in nums and freq(0,n,v) = D }. The set is nonempty because D is attained by at least one occurring value.
  Preconditions: len(nums) >= 1, len(nums) <= 50000, and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 49999. Let n = len(nums). For 0 <= l < h <= n, let freq(l,h,v) be the number of indices j with l <= j < h and nums[j] = v, and let degree(l,h) be the maximum of freq(l,h,v) over values v occurring in nums[l..h). Let D = degree(0,n). For a value v that occurs in nums, let first(v) be the smallest index i with nums[i]=v and last(v) the largest such index. -/
theorem spec_17 (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999) :
    ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (∃ v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums ∧
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) ∧
      (∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val ≤ (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) := by
  sorry

theorem spec_17_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_pos : 1 ≤ nums.val.length) (h_len_bound : nums.val.length ≤ 50000)
    (h_values : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 49999), ∀ r, Aegis.FindShortestSubArray.find_shortest_sub_array nums = ok r →
      (∃ v, occurs nums v ∧ freq nums 0 nums.val.length v = degreeAll nums ∧
        r.val = (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1) ∧
      (∀ v, occurs nums v → freq nums 0 nums.val.length v = degreeAll nums →
        r.val ≤ (lastOcc nums v : ℤ) - (firstOcc nums v : ℤ) + 1)) := by
  sorry

end AegisSpec.FindShortestSubArray
