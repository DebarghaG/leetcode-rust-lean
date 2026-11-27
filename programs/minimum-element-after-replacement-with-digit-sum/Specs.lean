import Aegis.MinElement.Code.Funs

/-!
# Specifications of `Aegis.MinElement.min_element`

LeetCode problem `minimum-element-after-replacement-with-digit-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinElement

def digitSum : Nat → Nat
  | 0 => 0
  | (n + 1) => (n + 1) % 10 + digitSum ((n + 1) / 10)
termination_by n => n
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by decide)

def digit_sum (n : Int) : Int := (digitSum n.toNat : Int)

def digitOneValues : List Int := [1, 10, 100, 1000, 10000]

/-- The function returns a result r, and r is the minimum of the values digit_sum(nums[i]) over all indices i with 0 <= i < len(nums): for every such i, r <= digit_sum(nums[i]), and there exists j with 0 <= j < len(nums) such that r = digit_sum(nums[j]).
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ digit_sum (nums.val[i]).val) ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = digit_sum (nums.val[j]).val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ digit_sum (nums.val[i]).val) ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = digit_sum (nums.val[j]).val)) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r) := by
  sorry

/-- The function returns a result r and r <= 36.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val ≤ 36 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val ≤ 36) := by
  sorry

/-- The function returns a result r and r >= 1.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and there exists an index j with 0 <= j < len(nums) such that r = digit_sum(nums[j]).
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = digit_sum (nums.val[j]).val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = digit_sum (nums.val[j]).val)) := by
  sorry

/-- The function returns a result r and for every i with 0 <= i < len(nums), r <= digit_sum(nums[i]).
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_6 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ digit_sum (nums.val[i]).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ digit_sum (nums.val[i]).val)) := by
  sorry

/-- The function returns a result r and r = digit_sum(nums[0]).
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. Additionally, len(nums) = 1. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_len_one : nums.val.length = 1) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      r.val = digit_sum (nums.val[0]'(by omega)).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_len_one : nums.val.length = 1), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      r.val = digit_sum (nums.val[0]'(by omega)).val) := by
  sorry

/-- The function returns a result r, and r is the minimum element of nums: for every i with 0 <= i < len(nums), r <= nums[i], and there exists j with 0 <= j < len(nums) such that r = nums[j].
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. Additionally, 1 <= nums[i] <= 9 for every i with 0 <= i < len(nums). For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_single_digit : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 9) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (nums.val[i]).val) ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = (nums.val[j]).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_single_digit : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 9), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (nums.val[i]).val) ∧
      (∃ (j : Nat) (hj : j < nums.val.length), r.val = (nums.val[j]).val)) := by
  sorry

/-- If there exists j with 0 <= j < len(nums) such that nums[j] is one of 1, 10, 100, 1000, or 10000, then the function returns a result r and r = 1.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_has_pow10 : ∃ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val ∈ digitOneValues) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val = 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_has_pow10 : ∃ (j : Nat) (hj : j < nums.val.length), (nums.val[j]).val ∈ digitOneValues), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns a result r and r = d.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. Additionally, there exists an integer d such that digit_sum(nums[i]) = d for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (d : Int)
    (h_const : ∀ (i : Nat) (hi : i < nums.val.length), digit_sum (nums.val[i]).val = d) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val = d := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (d : Int)
    (h_const : ∀ (i : Nat) (hi : i < nums.val.length), digit_sum (nums.val[i]).val = d), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ r.val = d) := by
  sorry

/-- Whenever min_element(nums) returns a result r and min_element(nums') returns a result r', one has r = r'.
  Preconditions: nums and nums' are slices of 64-bit integers, both satisfying 1 <= len <= 100 and all entries between 1 and 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. Assume len(nums) = len(nums') and there is a bijection pi from the indices of nums to the indices of nums' such that digit_sum(nums[i]) = digit_sum(nums'[pi(i)]) for every i with 0 <= i < len(nums). -/
theorem spec_11 (nums nums' : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_nonempty' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_in_range' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (pi : Nat → Nat)
    (h_pi_bound : ∀ (i : Nat) (hi : i < nums.val.length), pi i < nums'.val.length)
    (h_pi_inj : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
      pi i = pi j → i = j)
    (h_pi_surj : ∀ (j : Nat) (hj : j < nums'.val.length),
      ∃ (i : Nat) (hi : i < nums.val.length), pi i = j)
    (h_pi_digit_sum : ∀ (i : Nat) (hi : i < nums.val.length),
      digit_sum (nums.val[i]).val = digit_sum (nums'.val[pi i]'(h_pi_bound i hi)).val) :
    ∀ (r r' : Std.I64), Aegis.MinElement.min_element nums = ok r →
      Aegis.MinElement.min_element nums' = ok r' → r = r' := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_nonempty' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_in_range' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (pi : Nat → Nat)
    (h_pi_bound : ∀ (i : Nat) (hi : i < nums.val.length), pi i < nums'.val.length)
    (h_pi_inj : ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length),
      pi i = pi j → i = j)
    (h_pi_surj : ∀ (j : Nat) (hj : j < nums'.val.length),
      ∃ (i : Nat) (hi : i < nums.val.length), pi i = j)
    (h_pi_digit_sum : ∀ (i : Nat) (hi : i < nums.val.length),
      digit_sum (nums.val[i]).val = digit_sum (nums'.val[pi i]'(h_pi_bound i hi)).val), ∀ (r r' : Std.I64), Aegis.MinElement.min_element nums = ok r →
      Aegis.MinElement.min_element nums' = ok r' → r = r') := by
  sorry

/-- Whenever min_element(nums) returns a result r and min_element(nums') returns a result r', one has r <= r'.
  Preconditions: nums and nums' are slices of 64-bit integers, both satisfying 1 <= len <= 100 and all entries between 1 and 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. Assume len(nums) = len(nums') and for every i with 0 <= i < len(nums), digit_sum(nums[i]) <= digit_sum(nums'[i]). -/
theorem spec_12 (nums nums' : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_nonempty' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_in_range' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (h_le : ∀ (i : Nat) (hi : i < nums.val.length),
      digit_sum (nums.val[i]).val ≤ digit_sum (nums'.val[i]'(by omega)).val) :
    ∀ (r r' : Std.I64), Aegis.MinElement.min_element nums = ok r →
      Aegis.MinElement.min_element nums' = ok r' → r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_nonempty' : 1 ≤ nums'.val.length) (h_len_le' : nums'.val.length ≤ 100)
    (h_in_range' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 10000)
    (h_len_eq : nums.val.length = nums'.val.length)
    (h_le : ∀ (i : Nat) (hi : i < nums.val.length),
      digit_sum (nums.val[i]).val ≤ digit_sum (nums'.val[i]'(by omega)).val), ∀ (r r' : Std.I64), Aegis.MinElement.min_element nums = ok r →
      Aegis.MinElement.min_element nums' = ok r' → r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and r is divisible by 3.
  Preconditions: nums is a non-empty slice of 64-bit integers with 1 <= len(nums) <= 100, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10000. For a nonnegative integer n, digit_sum(n) denotes the sum of the decimal digits of n. Additionally, for every i with 0 <= i < len(nums), digit_sum(nums[i]) is divisible by 3. -/
theorem spec_13 (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_div3 : ∀ (i : Nat) (hi : i < nums.val.length), 3 ∣ digit_sum (nums.val[i]).val) :
    ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ 3 ∣ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_nonempty : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
    (h_in_range : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000)
    (h_div3 : ∀ (i : Nat) (hi : i < nums.val.length), 3 ∣ digit_sum (nums.val[i]).val), ∃ r : Std.I64, Aegis.MinElement.min_element nums = ok r ∧ 3 ∣ r.val) := by
  sorry

end AegisSpec.MinElement
