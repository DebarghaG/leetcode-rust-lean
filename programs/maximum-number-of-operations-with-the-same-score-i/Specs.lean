import Aegis.MaxOperations.Code.Funs

/-!
# Specifications of `Aegis.MaxOperations.max_operations`

LeetCode problem `maximum-number-of-operations-with-the-same-score-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxOperations

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def pairOk (nums : Slice Std.I64) (i : Nat) : Prop :=
    elem nums (2 * i) + elem nums (2 * i + 1) = elem nums 0 + elem nums 1

  def prefixOk (nums : Slice Std.I64) (k : Nat) : Prop :=
    ∀ i : Nat, i < k → pairOk nums i

  /-- The function returns a result r and r equals the largest integer k such that 0 <= k <= floor(len(nums)/2) and for every i with 0 <= i < k, nums[2*i] + nums[2*i+1] = nums[0] + nums[1].
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧
          IsGreatest {k : Nat | k ≤ nums.val.length / 2 ∧ prefixOk nums k} r.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧
            IsGreatest {k : Nat | k ≤ nums.val.length / 2 ∧ prefixOk nums k} r.val.toNat) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or overflow.
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64, Aegis.MaxOperations.max_operations nums = ok r) := by
    sorry

  /-- The function returns a result r and 1 <= r <= floor(len(nums)/2).
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (nums.val.length / 2 : Nat) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧
            1 ≤ r.val ∧ r.val ≤ (nums.val.length / 2 : Nat)) := by
    sorry

  /-- The function returns a result r and, for every i with 0 <= i < r, nums[2*i] + nums[2*i+1] = nums[0] + nums[1].
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧
          ∀ i : Nat, (i : Int) < r.val → pairOk nums i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧
            ∀ i : Nat, (i : Int) < r.val → pairOk nums i) := by
    sorry

  /-- The function returns a result r and, if 2*r + 1 < len(nums), then nums[2*r] + nums[2*r+1] != nums[0] + nums[1].
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧
          (2 * r.val + 1 < (nums.val.length : Int) → ¬ pairOk nums r.val.toNat) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧
            (2 * r.val + 1 < (nums.val.length : Int) → ¬ pairOk nums r.val.toNat)) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: 2 <= len(nums) <= 3 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 3)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 3)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r >= 2.
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; additionally len(nums) >= 4 and nums[2] + nums[3] = nums[0] + nums[1]. -/
  theorem spec_7 (nums : Slice Std.I64) (hlen_lo : 4 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
      (hpair : pairOk nums 1) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧ 2 ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 4 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
        (hpair : pairOk nums 1), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧ 2 ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = floor(len(nums)/2).
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; additionally for every i with 0 <= i < floor(len(nums)/2), nums[2*i] + nums[2*i+1] = nums[0] + nums[1]. -/
  theorem spec_8 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
      (hall : prefixOk nums (nums.val.length / 2)) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧ r.val = (nums.val.length / 2 : Nat) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
        (hall : prefixOk nums (nums.val.length / 2)), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧ r.val = (nums.val.length / 2 : Nat)) := by
    sorry

  /-- The function returns a result r and, if r = floor(len(nums)/2), then for every i with 0 <= i < floor(len(nums)/2), nums[2*i] + nums[2*i+1] = nums[0] + nums[1].
    Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000. -/
  theorem spec_9 (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
      (hlen_hi : nums.val.length ≤ 100)
      (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.MaxOperations.max_operations nums = ok r ∧
          (r.val = (nums.val.length / 2 : Nat) → prefixOk nums (nums.val.length / 2)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (hlen_lo : 2 ≤ nums.val.length)
        (hlen_hi : nums.val.length ≤ 100)
        (hbounds : ∀ i : Nat, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r : Std.I64,
          Aegis.MaxOperations.max_operations nums = ok r ∧
            (r.val = (nums.val.length / 2 : Nat) → prefixOk nums (nums.val.length / 2))) := by
    sorry

  end AegisSpec.MaxOperations
