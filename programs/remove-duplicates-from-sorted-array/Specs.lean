import Aegis.RemoveDuplicates.Code.Funs

/-!
# Specifications of `Aegis.RemoveDuplicates.remove_duplicates`

LeetCode problem `remove-duplicates-from-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.RemoveDuplicates
  set_option autoImplicit false

  namespace AegisSpec.RemoveDuplicates

  def distinctCount (l : List Int) : Nat :=
    l.dedup.length

  def countAdjacentSteps (p : Int → Int → Prop) [DecidableRel p] (l : List Int) : Nat :=
    (l.zip l.tail).countP fun q => decide (p q.1 q.2)

  def countAscents (l : List Int) : Nat :=
    countAdjacentSteps (fun a b => a < b) l

  def countEqualSteps (l : List Int) : Nat :=
    countAdjacentSteps (fun a b => a = b) l

  def countNonEqualSteps (l : List Int) : Nat :=
    countAdjacentSteps (fun a b => a ≠ b) l

  def IsStrictlyIncreasingSubsequence (l : List Int) (idx : List Nat) : Prop :=
    idx.Pairwise (· < ·) ∧
      (∀ j ∈ idx, j < l.length) ∧
      (idx.map (fun j => l.getD j 0)).Pairwise (· < ·)

  def IsLongestStrictlyIncreasingSubsequenceLength (l : List Int) (m : Nat) : Prop :=
    (∃ idx, IsStrictlyIncreasingSubsequence l idx ∧ idx.length = m) ∧
      ∀ idx, IsStrictlyIncreasingSubsequence l idx → idx.length ≤ m

  /-- The function returns a result r and r = |{nums[i] | 0 <= i < len(nums)}|, i.e., r is the number of distinct values in nums.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        r.val = (distinctCount (nums.val.map fun x => x.val) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          r.val = (distinctCount (nums.val.map fun x => x.val) : Int)) := by
    sorry

  /-- The function returns a result (it does not fail) for every input satisfying the preconditions.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r) := by
    sorry

  /-- The function returns a result r with 1 <= r <= len(nums).
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- The function returns a result r with r <= 201.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧ r.val ≤ 201 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧ r.val ≤ 201) := by
    sorry

  /-- The function returns a result r with r = 1.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]; len(nums) = 1. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val)
      (hlen_one : nums.val.length = 1) :
      ∃ r, remove_duplicates nums = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val)
        (hlen_one : nums.val.length = 1), ∃ r, remove_duplicates nums = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r with r = len(nums).
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] < nums[i+1]. -/
  theorem spec_6 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hstrict : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val < (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧ r.val = (nums.val.length : Int) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hstrict : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val < (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧ r.val = (nums.val.length : Int)) := by
    sorry

  /-- The function returns a result r with r = 1 + |{i | 1 <= i < len(nums) and nums[i] > nums[i-1]}|.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_7 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        r.val = 1 + (countAscents (nums.val.map fun x => x.val) : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          r.val = 1 + (countAscents (nums.val.map fun x => x.val) : Int)) := by
    sorry

  /-- The function returns a result r with r = len(nums) - |{i | 1 <= i < len(nums) and nums[i] = nums[i-1]}|.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_8 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        r.val = (nums.val.length : Int) - (countEqualSteps (nums.val.map fun x => x.val) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          r.val = (nums.val.length : Int) - (countEqualSteps (nums.val.map fun x => x.val) : Int)) := by
    sorry

  /-- The function returns a result r with r = 1 + |{i | 1 <= i < len(nums) and nums[i] != nums[i-1]}|.
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_9 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        r.val = 1 + (countNonEqualSteps (nums.val.map fun x => x.val) : Int) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          r.val = 1 + (countNonEqualSteps (nums.val.map fun x => x.val) : Int)) := by
    sorry

  /-- The function returns a result r that equals the length of the longest strictly increasing subsequence of nums. (A strictly increasing subsequence is a sequence of indices i_1 < i_2 < ... < i_m with nums[i_1] < nums[i_2] < ... < nums[i_m]; its length is m. r is the maximum such m.)
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_10 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        ∃ m : Nat, IsLongestStrictlyIncreasingSubsequenceLength
            (nums.val.map fun x => x.val) m ∧ r.val = (m : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          ∃ m : Nat, IsLongestStrictlyIncreasingSubsequenceLength
              (nums.val.map fun x => x.val) m ∧ r.val = (m : Int)) := by
    sorry

  /-- The function returns a result r. Then r = len(nums) if and only if for every i with 1 <= i < len(nums), nums[i] > nums[i-1].
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_11 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        (r.val = (nums.val.length : Int) ↔
          ∀ i (_hi1 : 1 ≤ i) (_hi2 : i < nums.val.length),
            (nums.val[i - 1]).val < (nums.val[i]).val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          (r.val = (nums.val.length : Int) ↔
            ∀ i (_hi1 : 1 ≤ i) (_hi2 : i < nums.val.length),
              (nums.val[i - 1]).val < (nums.val[i]).val)) := by
    sorry

  /-- The function returns a result r. Then r = 1 if and only if for every i with 1 <= i < len(nums), nums[i] = nums[i-1].
    Preconditions: 1 <= len(nums) <= 30000; for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100; for every i with 0 <= i < len(nums) - 1, nums[i] <= nums[i+1]. -/
  theorem spec_12 (nums : Slice I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
      (hbounds : ∀ i (_hi : i < nums.val.length),
        -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
      (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
      ∃ r, remove_duplicates nums = ok r ∧
        (r.val = 1 ↔
          ∀ i (_hi1 : 1 ≤ i) (_hi2 : i < nums.val.length),
            (nums.val[i - 1]).val = (nums.val[i]).val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 30000)
        (hbounds : ∀ i (_hi : i < nums.val.length),
          -100 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100)
        (hsorted : ∀ i (_hi : i < nums.val.length - 1), (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∃ r, remove_duplicates nums = ok r ∧
          (r.val = 1 ↔
            ∀ i (_hi1 : 1 ≤ i) (_hi2 : i < nums.val.length),
              (nums.val[i - 1]).val = (nums.val[i]).val)) := by
    sorry

  end AegisSpec.RemoveDuplicates
