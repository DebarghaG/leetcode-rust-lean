import Aegis.SmallestDivisor.Code.Funs

/-!
# Specifications of `Aegis.SmallestDivisor.smallest_divisor`

LeetCode problem `find-the-smallest-divisor-given-a-threshold`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SmallestDivisor

def ceilDiv (x d : Int) : Int := (x + (d - 1)) / d

def sumCeil (nums : List Std.I64) (d : Int) : Int :=
  (nums.map (fun x => ceilDiv x.val d)).sum

def sumEntry (nums : List Std.I64) : Int :=
  (nums.map (fun x => x.val)).sum

def maxEntry (nums : List Std.I64) : Int :=
  (nums.map (fun x => x.val)).foldr max 0

structure Pre (nums : Slice Std.I64) (threshold : Std.I64) : Prop where

  len_ge_one : 1 ≤ nums.val.length

  len_le_max : nums.val.length ≤ 50000

  entry_ge_one : ∀ x ∈ nums.val, 1 ≤ x.val

  entry_le_max : ∀ x ∈ nums.val, x.val ≤ 1000000

  threshold_ge_len : (nums.val.length : Int) ≤ threshold.val

  threshold_le_max : threshold.val ≤ 1000000

/-- The function returns a result r (it does not fail), and r is a positive integer that is the smallest positive integer d such that S(d) <= threshold, where S(d) = sum_{i=0}^{len(nums)-1} ceil(nums[i] / d) and ceil(x / d) denotes the smallest integer greater than or equal to the real quotient x / d.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_1 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∃ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r ∧
        1 ≤ r.val ∧
        sumCeil nums.val r.val ≤ threshold.val ∧
        ∀ d : Int, 1 ≤ d → sumCeil nums.val d ≤ threshold.val → r.val ≤ d := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∃ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r ∧
        1 ≤ r.val ∧
        sumCeil nums.val r.val ≤ threshold.val ∧
        ∀ d : Int, 1 ≤ d → sumCeil nums.val d ≤ threshold.val → r.val ≤ d) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (a 64-bit integer) and does not fail; in particular it does not overflow, panic, or go out of bounds.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_2 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∃ r : Std.I64, Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∃ r : Std.I64, Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r) := by
  sorry

/-- The returned r is a witness that a feasible divisor exists: S(r) <= threshold, where S(d) = sum_{i=0}^{len(nums)-1} ceil(nums[i] / d) with ceiling division.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_3 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        sumCeil nums.val r.val ≤ threshold.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        sumCeil nums.val r.val ≤ threshold.val) := by
  sorry

/-- For every integer d with 1 <= d < r, S(d) > threshold, where S(d) = sum_{i=0}^{len(nums)-1} ceil(nums[i] / d) with ceiling division.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_4 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ d : Int, 1 ≤ d → d < r.val → threshold.val < sumCeil nums.val d := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ d : Int, 1 ≤ d → d < r.val → threshold.val < sumCeil nums.val d) := by
  sorry

/-- For every integer d with r <= d and 1 <= d, S(d) <= threshold, where S(d) = sum_{i=0}^{len(nums)-1} ceil(nums[i] / d) with ceiling division.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_5 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ d : Int, r.val ≤ d → 1 ≤ d → sumCeil nums.val d ≤ threshold.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ d : Int, r.val ≤ d → 1 ≤ d → sumCeil nums.val d ≤ threshold.val) := by
  sorry

/-- The returned r satisfies r >= ceil((sum_{i=0}^{len(nums)-1} nums[i]) / threshold), where the outer ceil is the ceiling of the real quotient.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_6 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ceilDiv (sumEntry nums.val) threshold.val ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ceilDiv (sumEntry nums.val) threshold.val ≤ r.val) := by
  sorry

/-- The returned r satisfies r <= max_{0 <= i < len(nums)} nums[i].
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_7 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        r.val ≤ maxEntry nums.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        r.val ≤ maxEntry nums.val) := by
  sorry

/-- The returned r equals 1 if and only if sum_{i=0}^{len(nums)-1} nums[i] <= threshold.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_8 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        (r.val = 1 ↔ sumEntry nums.val ≤ threshold.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        (r.val = 1 ↔ sumEntry nums.val ≤ threshold.val)) := by
  sorry

/-- For every integer threshold' with threshold <= threshold' <= 1,000,000, if r' is the value returned by the function on nums and threshold', then r' <= r.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_9 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ (threshold' r' : Std.I64),
          threshold.val ≤ threshold'.val →
            threshold'.val ≤ 1000000 →
              Aegis.SmallestDivisor.smallest_divisor nums threshold' = ok r' → r'.val ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ (threshold' r' : Std.I64),
          threshold.val ≤ threshold'.val →
            threshold'.val ≤ 1000000 →
              Aegis.SmallestDivisor.smallest_divisor nums threshold' = ok r' → r'.val ≤ r.val) := by
  sorry

/-- For every slice nums' of 64-bit integers with len(nums') = len(nums) and with the same multiset of entries as nums, if r' is the value returned by the function on nums' and threshold, then r' = r.
  Preconditions: nums is a slice of 64-bit integers and threshold is a 64-bit integer such that 1 <= len(nums) <= 50,000, 1 <= nums[i] <= 1,000,000 for every i with 0 <= i < len(nums), and len(nums) <= threshold <= 1,000,000. -/
theorem spec_10 (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold) :
    ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ nums' : Slice Std.I64,
          nums'.val.length = nums.val.length →
            nums'.val.Perm nums.val →
              ∀ r' : Std.I64,
                Aegis.SmallestDivisor.smallest_divisor nums' threshold = ok r' → r' = r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (threshold : Std.I64) (h : Pre nums threshold), ∀ r : Std.I64,
      Aegis.SmallestDivisor.smallest_divisor nums threshold = ok r →
        ∀ nums' : Slice Std.I64,
          nums'.val.length = nums.val.length →
            nums'.val.Perm nums.val →
              ∀ r' : Std.I64,
                Aegis.SmallestDivisor.smallest_divisor nums' threshold = ok r' → r' = r) := by
  sorry

end AegisSpec.SmallestDivisor
