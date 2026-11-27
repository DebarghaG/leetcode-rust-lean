import Aegis.MaximumTripletValue.Code.Funs

/-!
# Specifications of `Aegis.MaximumTripletValue.maximum_triplet_value`

LeetCode problem `maximum-value-of-an-ordered-triplet-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumTripletValue

  def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def nval (nums : Slice Std.I64) (i : Nat) : ℤ :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def listMax (l : List ℤ) (d : ℤ) : ℤ := l.foldl (fun acc x => max acc x) d

  def prefixMax (nums : Slice Std.I64) (j : Nat) : ℤ := listMax ((vals nums).take j) 0

  def suffixMax (nums : Slice Std.I64) (j : Nat) : ℤ := listMax ((vals nums).drop (j + 1)) 0

  def jCandidates (nums : Slice Std.I64) : List ℤ :=
    (List.range (nums.val.length - 2)).map (fun t =>
      (prefixMax nums (t + 1) - nval nums (t + 1)) * suffixMax nums (t + 1))

  def bestJ (nums : Slice Std.I64) : ℤ := listMax (jCandidates nums) 0

  def tripletValues (nums : Slice Std.I64) : List ℤ :=
    (List.range nums.val.length).flatMap (fun i =>
      (List.range nums.val.length).flatMap (fun j =>
        (List.range nums.val.length).filterMap (fun k =>
          if i < j ∧ j < k then some ((nval nums i - nval nums j) * nval nums k) else none)))

  def tripletMax (nums : Slice Std.I64) : ℤ := listMax (tripletValues nums) 0

  /-- The function returns a result r and r = max( {0} ∪ { (nums[i] - nums[j]) * nums[k] | 0 <= i < j < k < len(nums) } ). Equivalently, r >= 0, every triplet value (nums[i] - nums[j]) * nums[k] for 0 <= i < j < k < len(nums) is at most r, and if r > 0 then some triplet attains value r.
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000) :
      ∃ r, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
        0 ≤ r.val ∧
        (∀ i j k, i < j → j < k → k < nums.val.length →
          (nval nums i - nval nums j) * nval nums k ≤ r.val) ∧
        (0 < r.val →
          ∃ i j k, i < j ∧ j < k ∧ k < nums.val.length ∧
            (nval nums i - nval nums j) * nval nums k = r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000), ∃ r, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r ∧
          0 ≤ r.val ∧
          (∀ i j k, i < j → j < k → k < nums.val.length →
            (nval nums i - nval nums j) * nval nums k ≤ r.val) ∧
          (0 < r.val →
            ∃ i j k, i < j ∧ j < k ∧ k < nums.val.length ∧
              (nval nums i - nval nums j) * nval nums k = r.val)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000) :
      ∃ r, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000), ∃ r, Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= 999999000000.
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      r.val ≤ 999999000000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), r.val ≤ 999999000000) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i, j, k with 0 <= i < j < k < len(nums), we have (nums[i] - nums[j]) * nums[k] <= 0.
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      r.val = 0 ↔
        ∀ i j k, i < j → j < k → k < nums.val.length →
          (nval nums i - nval nums j) * nval nums k ≤ 0 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), r.val = 0 ↔
          ∀ i j k, i < j → j < k → k < nums.val.length →
            (nval nums i - nval nums j) * nval nums k ≤ 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if for every i, j with 0 <= i < j <= len(nums)-2, we have nums[i] <= nums[j].
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      r.val = 0 ↔
        ∀ i j, i < j → j ≤ nums.val.length - 2 → nval nums i ≤ nval nums j := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), r.val = 0 ↔
          ∀ i j, i < j → j ≤ nums.val.length - 2 → nval nums i ≤ nval nums j) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 1 <= j <= len(nums)-2, we have r >= (M_j - nums[j]) * N_j, where M_j = max{ nums[i] | 0 <= i < j } and N_j = max{ nums[k] | j < k < len(nums) }.
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      ∀ j, 1 ≤ j → j ≤ nums.val.length - 2 →
        (prefixMax nums j - nval nums j) * suffixMax nums j ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), ∀ j, 1 ≤ j → j ≤ nums.val.length - 2 →
          (prefixMax nums j - nval nums j) * suffixMax nums j ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r with r > 0, for every i, j, k with 0 <= i < j < k < len(nums), if (nums[i] - nums[j]) * nums[k] = r, then nums[i] > nums[j].
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r)
      (hpos : 0 < r.val) :
      ∀ i j k, i < j → j < k → k < nums.val.length →
        (nval nums i - nval nums j) * nval nums k = r.val → nval nums j < nval nums i := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r)
        (hpos : 0 < r.val), ∀ i j k, i < j → j < k → k < nums.val.length →
          (nval nums i - nval nums j) * nval nums k = r.val → nval nums j < nval nums i) := by
    sorry

  /-- Whenever the function returns a result r, r = max({0} union { (M_j - nums[j]) * N_j | 1 <= j <= len(nums)-2 }), where M_j = max{ nums[i] | 0 <= i < j } and N_j = max{ nums[k] | j < k < len(nums) }.
    Preconditions: len(nums) >= 3 and len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
      (r : Std.I64)
      (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r) :
      r.val = bestJ nums := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 3 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length → 1 ≤ nval nums i ∧ nval nums i ≤ 1000000)
        (r : Std.I64)
        (hres : Aegis.MaximumTripletValue.maximum_triplet_value nums = ok r), r.val = bestJ nums) := by
    sorry

  end AegisSpec.MaximumTripletValue
