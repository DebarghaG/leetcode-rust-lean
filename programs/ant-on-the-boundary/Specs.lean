import Aegis.ReturnToBoundaryCount.Code.Funs

/-!
# Specifications of `Aegis.ReturnToBoundaryCount.return_to_boundary_count`

LeetCode problem `ant-on-the-boundary`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ReturnToBoundaryCount

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def prefixSum (nums : Slice Std.I64) (i : Nat) : Int :=
    ((List.range (i + 1)).map (fun k => elem nums k)).sum

  def zeroPrefixCount (nums : Slice Std.I64) : Nat :=
    ((List.range nums.val.length).filter (fun i => prefixSum nums i = 0)).length

  def notBothConsecutiveZero (nums : Slice Std.I64) : Prop :=
    ∀ i, i + 1 < nums.val.length → ¬ (prefixSum nums i = 0 ∧ prefixSum nums (i + 1) = 0)

  /-- The function returns a result: there exists an integer r such that return_to_boundary_count nums = Result.ok r. It does not fail, overflow, or panic on these inputs.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10) :
      ∃ r : Std.I64,
        Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10), ∃ r : Std.I64,
          Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) := by
    sorry

  /-- Let n = len(nums). For 0 <= i < n let S(i) = nums[0] + nums[1] + ... + nums[i] (ordinary integer sum). Whenever the function returns a result r, r is exactly the number of indices i with 0 <= i < n such that S(i) = 0.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      r.val = (zeroPrefixCount nums : Int) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), r.val = (zeroPrefixCount nums : Int)) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), 0 ≤ r.val) := by
    sorry

  /-- Let n = len(nums). Whenever the function returns a result r, r <= n div 2 (integer division; equivalently r <= floor(n/2)).
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      r.val ≤ ((nums.val.length / 2 : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), r.val ≤ ((nums.val.length / 2 : Nat) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10; len(nums) = 1. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (hlen : nums.val.length = 1)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      r.val = 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (hlen : nums.val.length = 1)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if nums[0] + nums[1] = 0, and r = 0 otherwise.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10; len(nums) = 2. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (hlen : nums.val.length = 2)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      r.val = if elem nums 0 + elem nums 1 = 0 then (1 : Int) else 0 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (hlen : nums.val.length = 2)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), r.val = if elem nums 0 + elem nums 1 = 0 then (1 : Int) else 0) := by
    sorry

  /-- Let n = len(nums) and for 0 <= i < n let S(i) = nums[0] + ... + nums[i]. Whenever the function returns a result r, r = 0 if and only if there is no index i with 0 <= i < n and S(i) = 0.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      (r.val = 0 ↔ ∀ i, i < nums.val.length → prefixSum nums i ≠ 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), (r.val = 0 ↔ ∀ i, i < nums.val.length → prefixSum nums i ≠ 0)) := by
    sorry

  /-- Let n = len(nums) and for 0 <= i < n let S(i) = nums[0] + ... + nums[i]. Whenever the function returns a result r with r > 0, there exists an index i such that 0 <= i < n, S(i) = 0, and S(j) != 0 for every j with 0 <= j < i.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
      (hpos : 0 < r.val) :
      ∃ i, i < nums.val.length ∧ prefixSum nums i = 0 ∧
        ∀ j, j < i → prefixSum nums j ≠ 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
        (hpos : 0 < r.val), ∃ i, i < nums.val.length ∧ prefixSum nums i = 0 ∧
          ∀ j, j < i → prefixSum nums j ≠ 0) := by
    sorry

  /-- Let n = len(nums) and S(n-1) = nums[0] + ... + nums[n-1] be the final position. Whenever the function returns a result r, if S(n-1) = 0 then r >= 1.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
      (hfinal : prefixSum nums (nums.val.length - 1) = 0) :
      1 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
        (hfinal : prefixSum nums (nums.val.length - 1) = 0), 1 ≤ r.val) := by
    sorry

  /-- Let m be the list of length len(nums) with m[i] = -nums[i] for every i with 0 <= i < len(nums). Whenever return_to_boundary_count nums returns r and return_to_boundary_count m returns r_m, we have r = r_m.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (m : Slice Std.I64)
      (hlen_m : m.val.length = nums.val.length)
      (hneg : ∀ i, i < nums.val.length → elem m i = - (elem nums i))
      (r rm : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
      (hres_m : Aegis.ReturnToBoundaryCount.return_to_boundary_count m = ok rm) :
      r.val = rm.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (m : Slice Std.I64)
        (hlen_m : m.val.length = nums.val.length)
        (hneg : ∀ i, i < nums.val.length → elem m i = - (elem nums i))
        (r rm : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r)
        (hres_m : Aegis.ReturnToBoundaryCount.return_to_boundary_count m = ok rm), r.val = rm.val) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: 1 <= len(nums) <= 100; for every i with 0 <= i < len(nums), nums[i] != 0 and -10 <= nums[i] <= 10; len(nums) >= 2; nums[0] + nums[1] = 0. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
      (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
      (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
      (hlen : 2 ≤ nums.val.length)
      (hpair : elem nums 0 + elem nums 1 = 0)
      (r : Std.I64)
      (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 100)
        (hnonzero : ∀ i, i < nums.val.length → elem nums i ≠ 0)
        (hrange : ∀ i, i < nums.val.length → -10 ≤ elem nums i ∧ elem nums i ≤ 10)
        (hlen : 2 ≤ nums.val.length)
        (hpair : elem nums 0 + elem nums 1 = 0)
        (r : Std.I64)
        (hres : Aegis.ReturnToBoundaryCount.return_to_boundary_count nums = ok r), 1 ≤ r.val) := by
    sorry

  end AegisSpec.ReturnToBoundaryCount
