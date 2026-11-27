import Aegis.GetSumAbsoluteDifferences.Code.Funs

/-!
# Specifications of `Aegis.GetSumAbsoluteDifferences.get_sum_absolute_differences`

LeetCode problem `sum-of-absolute-differences-in-a-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.GetSumAbsoluteDifferences (get_sum_absolute_differences)

namespace AegisSpec.GetSumAbsoluteDifferences

def absDiff (a b : Int) : Int := if a ≥ b then a - b else b - a

def numsInts (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def sumAbsDiff (x : Int) (l : List Int) : Int := (l.map (fun y => absDiff x y)).sum

def sumAbsDiffAtNe (l : List Int) (i : Nat) : Int := sumAbsDiff (l[i]!) (l.eraseIdx i)

def sumOfFirst (r : alloc.vec.Vec I64) (n : Nat) : Int :=
  ((List.range n).map (fun i => (r.val[i]!).val)).sum

def pairDiffSum (l : List Int) : Int :=
  (l.zipIdx.flatMap (fun p => (l.drop (p.2 + 1)).map (fun y => y - p.1))).sum

/-- Whenever the function returns a result r, for every index i with 0 <= i < len(nums), r[i] equals the sum over all indices j with 0 <= j < len(nums) and j != i of |nums[i] - nums[j]|, where |a-b| denotes the nonnegative absolute difference of the two integers (a-b if a >= b, and b-a otherwise).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_1 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        (r.val[i]!).val = sumAbsDiffAtNe (numsInts nums) i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        (r.val[i]!).val = sumAbsDiffAtNe (numsInts nums) i) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums); that is, r has exactly one entry for each index of nums and no extra entries.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_2 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r → r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r → r.val.length = nums.val.length) := by
  sorry

/-- For every input nums satisfying the preconditions, the function returns a result r (the Lean Result is Ok r); it does not fail, panic, or overflow.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_3 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∃ r, get_sum_absolute_differences nums = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∃ r, get_sum_absolute_differences nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] >= 0.
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_4 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length → 0 ≤ (r.val[i]!).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length → 0 ≤ (r.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] <= (len(nums)-1) * (nums[len(nums)-1] - nums[0]).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_5 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        (r.val[i]!).val
          ≤ ((nums.val.length : Int) - 1)
              * ((nums.val[nums.val.length - 1]!).val - (nums.val[0]!).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        (r.val[i]!).val
          ≤ ((nums.val.length : Int) - 1)
              * ((nums.val[nums.val.length - 1]!).val - (nums.val[0]!).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), r[i] = 0 if and only if nums[0] = nums[len(nums)-1] (equivalently, all entries of nums are equal).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_6 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        ((r.val[i]!).val = 0
          ↔ (nums.val[0]!).val = (nums.val[nums.val.length - 1]!).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i < nums.val.length →
        ((r.val[i]!).val = 0
          ↔ (nums.val[0]!).val = (nums.val[nums.val.length - 1]!).val)) := by
  sorry

/-- Whenever the function returns a result r, if len(nums) = 2, then r[0] = r[1] = nums[1] - nums[0].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_7 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      nums.val.length = 2 →
        (r.val[0]!).val = (r.val[1]!).val ∧
          (r.val[0]!).val = (nums.val[1]!).val - (nums.val[0]!).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      nums.val.length = 2 →
        (r.val[0]!).val = (r.val[1]!).val ∧
          (r.val[0]!).val = (nums.val[1]!).val - (nums.val[0]!).val) := by
  sorry

/-- Whenever the function returns a result r, r[0] = (sum_{j=0}^{len(nums)-1} nums[j]) - len(nums) * nums[0].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_8 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      (r.val[0]!).val
        = (numsInts nums).sum - (nums.val.length : Int) * (nums.val[0]!).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      (r.val[0]!).val
        = (numsInts nums).sum - (nums.val.length : Int) * (nums.val[0]!).val) := by
  sorry

/-- Whenever the function returns a result r, r[len(nums)-1] = len(nums) * nums[len(nums)-1] - (sum_{j=0}^{len(nums)-1} nums[j]).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_9 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      (r.val[nums.val.length - 1]!).val
        = (nums.val.length : Int) * (nums.val[nums.val.length - 1]!).val
            - (numsInts nums).sum := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      (r.val[nums.val.length - 1]!).val
        = (nums.val.length : Int) * (nums.val[nums.val.length - 1]!).val
            - (numsInts nums).sum) := by
  sorry

/-- Whenever the function returns a result r, the sum over i=0 to len(nums)-1 of r[i] equals 2 * (sum over all pairs (i,j) with 0 <= i < j < len(nums) of (nums[j] - nums[i])).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_10 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      sumOfFirst r nums.val.length = 2 * pairDiffSum (numsInts nums) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      sumOfFirst r nums.val.length = 2 * pairDiffSum (numsInts nums)) := by
  sorry

/-- Whenever the function returns a result r on nums, for every integer c such that the slice nums' defined by nums'[i] = nums[i] + c for all i also satisfies the same preconditions (in particular 1 <= nums[i] + c <= 10000 for every i), if the function returns a result r' on nums', then r'[i] = r[i] for every i with 0 <= i < len(nums).
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_11 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (c : Int) (nums' : Slice I64)
    (hlen' : nums'.val.length = nums.val.length)
    (hshift : ∀ i, i < nums.val.length → (nums'.val[i]!).val = (nums.val[i]!).val + c)
    (hsorted' :
      ∀ i, i + 1 < nums'.val.length → (nums'.val[i]!).val ≤ (nums'.val[i + 1]!).val)
    (hbounded' :
      ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ r', get_sum_absolute_differences nums' = ok r' →
        ∀ i, i < nums.val.length → (r'.val[i]!).val = (r.val[i]!).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000)
    (c : Int) (nums' : Slice I64)
    (hlen' : nums'.val.length = nums.val.length)
    (hshift : ∀ i, i < nums.val.length → (nums'.val[i]!).val = (nums.val[i]!).val + c)
    (hsorted' :
      ∀ i, i + 1 < nums'.val.length → (nums'.val[i]!).val ≤ (nums'.val[i + 1]!).val)
    (hbounded' :
      ∀ i, i < nums'.val.length → 1 ≤ (nums'.val[i]!).val ∧ (nums'.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ r', get_sum_absolute_differences nums' = ok r' →
        ∀ i, i < nums.val.length → (r'.val[i]!).val = (r.val[i]!).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums)-1 and 2*i <= len(nums)-2, r[i] >= r[i+1].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_12 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i + 1 < nums.val.length → 2 * i ≤ nums.val.length - 2 →
        (r.val[i]!).val ≥ (r.val[i + 1]!).val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i + 1 < nums.val.length → 2 * i ≤ nums.val.length - 2 →
        (r.val[i]!).val ≥ (r.val[i + 1]!).val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums)-1 and 2*i >= len(nums)-2, r[i] <= r[i+1].
  Preconditions: nums is a slice of 64-bit integers with 2 <= len(nums) <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]; and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. -/
theorem spec_13 (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000) :
    ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i + 1 < nums.val.length → nums.val.length - 2 ≤ 2 * i →
        (r.val[i]!).val ≤ (r.val[i + 1]!).val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lo : 2 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
    (hsorted : ∀ i, i + 1 < nums.val.length → (nums.val[i]!).val ≤ (nums.val[i + 1]!).val)
    (hbounded : ∀ i, i < nums.val.length → 1 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 10000), ∀ r, get_sum_absolute_differences nums = ok r →
      ∀ i, i + 1 < nums.val.length → nums.val.length - 2 ≤ 2 * i →
        (r.val[i]!).val ≤ (r.val[i + 1]!).val) := by
  sorry

end AegisSpec.GetSumAbsoluteDifferences
