import Aegis.PrefixesDivBy5.Code.Funs

/-!
# Specifications of `Aegis.PrefixesDivBy5.prefixes_div_by5`

LeetCode problem `binary-prefix-divisible-by-5`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PrefixesDivBy5

def ival (nums : Slice Std.I64) (j : Nat) : Int :=
  ((nums.val[j]?).map (fun x => x.val)).getD 0

def prefixVal (nums : Slice Std.I64) (i : Nat) : Int :=
  ((List.range (i + 1)).map (fun j => ival nums j * (2 : Int) ^ (i - j))).sum

def rem (nums : Slice Std.I64) (i : Nat) : Int :=
  prefixVal nums i % 5

/-- For every i with 0 <= i < len(nums), define X_i = sum_{j=0}^{i} nums[j] * 2^(i-j). Whenever prefixes_div_by5 nums returns a result r, it holds that len(r) = len(nums) and, for every i with 0 <= i < len(nums), r[i] = true if and only if there exists an integer q with X_i = 5*q.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) :
    r.val.length = nums.val.length ∧
      (∀ i, i < nums.val.length →
        (r.val[i]? = some true ↔ ∃ q : Int, prefixVal nums i = 5 * q)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r), r.val.length = nums.val.length ∧
      (∀ i, i < nums.val.length →
        (r.val[i]? = some true ↔ ∃ q : Int, prefixVal nums i = 5 * q))) := by
  sorry

/-- For every nums satisfying the preconditions, the call prefixes_div_by5 nums returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1) :
    ∃ r : alloc.vec.Vec Bool, Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1), ∃ r : alloc.vec.Vec Bool, Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) := by
  sorry

/-- Whenever prefixes_div_by5 nums returns a result r, for every i and k with 0 <= i, 1 <= k, and i+k < len(nums), if nums[j] = 0 for every j with i < j <= i+k, then r[i+k] = r[i].
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) :
    ∀ i k : Nat, 1 ≤ k → i + k < nums.val.length →
      (∀ j, i < j → j ≤ i + k → ival nums j = 0) → r.val[i + k]? = r.val[i]? := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r), ∀ i k : Nat, 1 ≤ k → i + k < nums.val.length →
      (∀ j, i < j → j ≤ i + k → ival nums j = 0) → r.val[i + k]? = r.val[i]?) := by
  sorry

/-- Whenever prefixes_div_by5 nums returns a result r, if nums[j] = 1 for every j with 0 <= j < len(nums), then for every i with 0 <= i < len(nums), r[i] = true if and only if (i+1) mod 4 = 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) :
    (∀ j, j < nums.val.length → ival nums j = 1) →
      ∀ i, i < nums.val.length → (r.val[i]? = some true ↔ (i + 1) % 4 = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r), (∀ j, j < nums.val.length → ival nums j = 1) →
      ∀ i, i < nums.val.length → (r.val[i]? = some true ↔ (i + 1) % 4 = 0)) := by
  sorry

/-- Whenever prefixes_div_by5 nums returns a result r, for every i with 0 <= i and i+1 < len(nums), if r[i] = true, then r[i+1] = true if and only if nums[i+1] = 0.
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) :
    ∀ i, i + 1 < nums.val.length → r.val[i]? = some true →
      (r.val[i + 1]? = some true ↔ ival nums (i + 1) = 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r), ∀ i, i + 1 < nums.val.length → r.val[i]? = some true →
      (r.val[i + 1]? = some true ↔ ival nums (i + 1) = 0)) := by
  sorry

/-- For every i with 0 <= i < len(nums), define X_i = sum_{j=0}^{i} nums[j] * 2^(i-j), and let rem_i be the unique integer with 0 <= rem_i < 5 and X_i congruent to rem_i modulo 5. Whenever prefixes_div_by5 nums returns a result r, it holds that rem_0 = nums[0], that rem_{i+1} = (2*rem_i + nums[i+1]) mod 5 for every i with 0 <= i and i+1 < len(nums), and that r[i] = true if and only if rem_i = 0 for every i with 0 <= i < len(nums).
  Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every j with 0 <= j < len(nums), nums[j] = 0 or nums[j] = 1. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r) :
    rem nums 0 = ival nums 0 ∧
      (∀ i, i + 1 < nums.val.length →
        rem nums (i + 1) = (2 * rem nums i + ival nums (i + 1)) % 5) ∧
        (∀ i, i < nums.val.length → (r.val[i]? = some true ↔ rem nums i = 0)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100000)
    (h_bin : ∀ j, j < nums.val.length → ival nums j = 0 ∨ ival nums j = 1)
    (r : alloc.vec.Vec Bool) (hr : Aegis.PrefixesDivBy5.prefixes_div_by5 nums = ok r), rem nums 0 = ival nums 0 ∧
      (∀ i, i + 1 < nums.val.length →
        rem nums (i + 1) = (2 * rem nums i + ival nums (i + 1)) % 5) ∧
        (∀ i, i < nums.val.length → (r.val[i]? = some true ↔ rem nums i = 0))) := by
  sorry

end AegisSpec.PrefixesDivBy5
