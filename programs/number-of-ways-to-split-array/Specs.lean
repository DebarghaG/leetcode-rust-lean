import Aegis.WaysToSplitArray.Code.Funs

/-!
# Specifications of `Aegis.WaysToSplitArray.ways_to_split_array`

LeetCode problem `number-of-ways-to-split-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.WaysToSplitArray

  namespace AegisSpec.WaysToSplitArray

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def prefixSum (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    ((nums.val.take (i + 1)).map (fun x => x.val)).sum

  def suffixSum (nums : Slice Std.I64) (i : ℕ) : ℤ :=
    ((nums.val.drop (i + 1)).map (fun x => x.val)).sum

  def totalSum (nums : Slice Std.I64) : ℤ := (vals nums).sum

  def validSplitIndices (nums : Slice Std.I64) (n : ℕ) : List ℕ :=
    (List.range (n - 1)).filter (fun i => suffixSum nums i ≤ prefixSum nums i)

  def invalidSplitIndices (nums : Slice Std.I64) (n : ℕ) : List ℕ :=
    (List.range (n - 1)).filter (fun i => prefixSum nums i < suffixSum nums i)

  def ceilHalf (n : ℕ) : ℤ := (((n - 2) + 1) / 2 : ℕ)

  def floorHalf (n : ℕ) : ℤ := (((n - 2) / 2 : ℕ) : ℤ)

  /-- For every integer i with 0 <= i < n-1, define P(i) = sum_{k=0}^{i} nums[k] and S(i) = sum_{k=i+1}^{n-1} nums[k]. Let V = { i | 0 <= i < n-1 and P(i) >= S(i) }. The function returns a result r and r equals the number of elements of V, i.e. r is exactly the number of valid splits in nums.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. All sums below are ordinary integer sums of the i64 values. -/
  theorem spec_1 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        r.val = ((validSplitIndices nums n).length : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          r.val = ((validSplitIndices nums n).length : ℤ)) := by
    sorry

  /-- For every nums satisfying the preconditions, ways_to_split_array(nums) returns a result; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n-1.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧ 0 ≤ r.val ∧ r.val ≤ (n : ℤ) - 1) := by
    sorry

  /-- Let T = sum_{k=0}^{n-1} nums[k]. The function returns a result r and r = |{ i | 0 <= i < n-1 and 2 * (sum_{k=0}^{i} nums[k]) >= T }|.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        r.val = (((List.range (n - 1)).filter
          (fun i => 2 * prefixSum nums i ≥ totalSum nums)).length : ℤ) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          r.val = (((List.range (n - 1)).filter
            (fun i => 2 * prefixSum nums i ≥ totalSum nums)).length : ℤ)) := by
    sorry

  /-- Let W = { i | 0 <= i < n-1 and sum_{k=0}^{i} nums[k] < sum_{k=i+1}^{n-1} nums[k] }. The function returns a result r and r = (n-1) - |W|.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        r.val = (n : ℤ) - 1 - ((invalidSplitIndices nums n).length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          r.val = (n : ℤ) - 1 - ((invalidSplitIndices nums n).length : ℤ)) := by
    sorry

  /-- The function returns a result r and r = n-1 if and only if for every i with 0 <= i < n-1, sum_{k=0}^{i} nums[k] >= sum_{k=i+1}^{n-1} nums[k].
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        (r.val = (n : ℤ) - 1 ↔ ∀ i : ℕ, i < n - 1 → prefixSum nums i ≥ suffixSum nums i) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          (r.val = (n : ℤ) - 1 ↔ ∀ i : ℕ, i < n - 1 → prefixSum nums i ≥ suffixSum nums i)) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if for every i with 0 <= i < n-1, sum_{k=0}^{i} nums[k] < sum_{k=i+1}^{n-1} nums[k].
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        (r.val = 0 ↔ ∀ i : ℕ, i < n - 1 → prefixSum nums i < suffixSum nums i) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          (r.val = 0 ↔ ∀ i : ℕ, i < n - 1 → prefixSum nums i < suffixSum nums i)) := by
    sorry

  /-- The function returns a result r and r > 0 if and only if there exists an integer i with 0 <= i < n-1 such that sum_{k=0}^{i} nums[k] >= sum_{k=i+1}^{n-1} nums[k].
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        (0 < r.val ↔ ∃ i : ℕ, i < n - 1 ∧ prefixSum nums i ≥ suffixSum nums i) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          (0 < r.val ↔ ∃ i : ℕ, i < n - 1 ∧ prefixSum nums i ≥ suffixSum nums i)) := by
    sorry

  /-- The function returns a result r and, if nums[k] >= 0 for every k with 0 <= k < n, then there exists an integer t with 0 <= t <= n-1 such that: for every i with 0 <= i < n-1, the split i is valid, meaning sum_{k=0}^{i} nums[k] >= sum_{k=i+1}^{n-1} nums[k], if and only if i >= t; and r = n-1-t.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        ((∀ x ∈ vals nums, 0 ≤ x) →
          ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) - 1 ∧
            (∀ i : ℕ, i < n - 1 → (prefixSum nums i ≥ suffixSum nums i ↔ (i : ℤ) ≥ t)) ∧
            r.val = (n : ℤ) - 1 - t) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          ((∀ x ∈ vals nums, 0 ≤ x) →
            ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) - 1 ∧
              (∀ i : ℕ, i < n - 1 → (prefixSum nums i ≥ suffixSum nums i ↔ (i : ℤ) ≥ t)) ∧
              r.val = (n : ℤ) - 1 - t)) := by
    sorry

  /-- The function returns a result r and, if nums[k] <= 0 for every k with 0 <= k < n, then there exists an integer t with -1 <= t <= n-2 such that: for every i with 0 <= i < n-1, the split i is valid, meaning sum_{k=0}^{i} nums[k] >= sum_{k=i+1}^{n-1} nums[k], if and only if i <= t; and r = t+1.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        ((∀ x ∈ vals nums, x ≤ 0) →
          ∃ t : ℤ, -1 ≤ t ∧ t ≤ (n : ℤ) - 2 ∧
            (∀ i : ℕ, i < n - 1 → (prefixSum nums i ≥ suffixSum nums i ↔ (i : ℤ) ≤ t)) ∧
            r.val = t + 1) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          ((∀ x ∈ vals nums, x ≤ 0) →
            ∃ t : ℤ, -1 ≤ t ∧ t ≤ (n : ℤ) - 2 ∧
              (∀ i : ℕ, i < n - 1 → (prefixSum nums i ≥ suffixSum nums i ↔ (i : ℤ) ≤ t)) ∧
              r.val = t + 1)) := by
    sorry

  /-- The function returns a result r and, for every positive integer c such that -100000 <= c * nums[k] <= 100000 for every k with 0 <= k < n, the call ways_to_split_array(nums_c) on the array nums_c[k] = c * nums[k] also returns a result and that result equals r.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_11 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
        ∀ (c : ℤ), 1 ≤ c →
          (∀ x ∈ vals nums, -100000 ≤ c * x ∧ c * x ≤ 100000) →
          ∀ nums_c : Slice Std.I64, vals nums_c = (vals nums).map (fun x => c * x) →
            ∃ r_c : Std.I64, ways_to_split_array nums_c = ok r_c ∧ r_c.val = r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          ∀ (c : ℤ), 1 ≤ c →
            (∀ x ∈ vals nums, -100000 ≤ c * x ∧ c * x ≤ 100000) →
            ∀ nums_c : Slice Std.I64, vals nums_c = (vals nums).map (fun x => c * x) →
              ∃ r_c : Std.I64, ways_to_split_array nums_c = ok r_c ∧ r_c.val = r.val) := by
    sorry

  /-- If there is an integer c such that nums[k] = c for every k with 0 <= k < n, then the function returns a result r and: if c > 0 then r = (n-1) - ceil_half; if c = 0 then r = n-1; if c < 0 then r = floor_half + 1, where ceil_half is the least integer q with 2q >= n-2 and floor_half is the greatest integer q with 2q <= n-2.
    Preconditions: n = len(nums); 2 <= n <= 100000; for every k with 0 <= k < n, -100000 <= nums[k] <= 100000. -/
  theorem spec_12 (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
      (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
      (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000) :
      ∀ c : ℤ, (∀ x ∈ vals nums, x = c) →
        ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
          (0 < c → r.val = (n : ℤ) - 1 - ceilHalf n) ∧
          (c = 0 → r.val = (n : ℤ) - 1) ∧
          (c < 0 → r.val = floorHalf n + 1) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = nums.val.length)
        (hn_lb : 2 ≤ n) (hn_ub : n ≤ 100000)
        (h_bound : ∀ x ∈ vals nums, -100000 ≤ x ∧ x ≤ 100000), ∀ c : ℤ, (∀ x ∈ vals nums, x = c) →
          ∃ r : Std.I64, ways_to_split_array nums = ok r ∧
            (0 < c → r.val = (n : ℤ) - 1 - ceilHalf n) ∧
            (c = 0 → r.val = (n : ℤ) - 1) ∧
            (c < 0 → r.val = floorHalf n + 1)) := by
    sorry

  end AegisSpec.WaysToSplitArray
