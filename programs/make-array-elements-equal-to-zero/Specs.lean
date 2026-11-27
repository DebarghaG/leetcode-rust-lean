import Aegis.CountValidSelections.Code.Funs

/-!
# Specifications of `Aegis.CountValidSelections.count_valid_selections`

LeetCode problem `make-array-elements-equal-to-zero`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountValidSelections (count_valid_selections)

namespace AegisSpec.CountValidSelections

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def leftSum (l : List Int) (i : Nat) : Int := (l.take i).sum

def rightSum (l : List Int) (i : Nat) : Int := (l.drop (i + 1)).sum

def contrib (l : List Int) (i : Nat) : Int :=
  if leftSum l i = rightSum l i then 2
  else if (leftSum l i - rightSum l i).natAbs = 1 then 1
  else 0

def weightSum (l : List Int) : Int :=
  ((List.range l.length).map (fun i => if l[i]? = some (0 : Int) then contrib l i else 0)).sum

def zeroCount (l : List Int) : Nat := l.countP (fun x => x = 0)

def zeroIdx (l : List Int) : List Nat :=
  (List.range l.length).filter (fun i => l[i]? = some (0 : Int))

def balancedZeroCount (l : List Int) : Nat :=
  ((zeroIdx l).filter (fun i => leftSum l i = rightSum l i)).length

def adjacentZeroCount (l : List Int) : Nat :=
  ((zeroIdx l).filter (fun i => (leftSum l i - rightSum l i).natAbs = 1)).length

/-- Whenever the function returns a result r, r equals the sum over all indices i with 0 <= i < n and nums[i] = 0 of c(i), where L(i) = sum_{0 <= j < i} nums[j], R(i) = sum_{i < j < n} nums[j], and c(i) = 2 if L(i) = R(i), c(i) = 1 if |L(i) - R(i)| = 1, and c(i) = 0 otherwise.
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_1 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    r.val = weightSum (vals nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), r.val = weightSum (vals nums)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, panic, overflow, or access an out-of-range index.
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_2 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0) :
    ∃ r, count_valid_selections nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0), ∃ r, count_valid_selections nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= 2*z, where z is the number of indices i with 0 <= i < n and nums[i] = 0.
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_3 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    0 ≤ r.val ∧ r.val ≤ 2 * (zeroCount (vals nums) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), 0 ≤ r.val ∧ r.val ≤ 2 * (zeroCount (vals nums) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = 2*n, where n = len(nums).
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, nums[i] = 0. -/
theorem spec_4 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_all : ∀ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    r.val = 2 * (nums.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_all : ∀ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), r.val = 2 * (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = n - 1, where n = len(nums).
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; there exists an index i with nums[i] = 0; and sum_{i=0}^{n-1} nums[i] = 1. -/
theorem spec_5 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_sum : (vals nums).sum = 1)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    r.val = (nums.val.length : Int) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_sum : (vals nums).sum = 1)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), r.val = (nums.val.length : Int) - 1) := by
  sorry

/-- Whenever the function returns a result r, r = 4 if nums[0] = 0 and nums[1] = 0; r = 1 if nums[0] + nums[1] = 1; and r = 0 if nums[0] + nums[1] >= 2.
  Preconditions: Let n = len(nums). The input satisfies n = 2, 0 <= nums[0] <= 100, 0 <= nums[1] <= 100, and at least one of nums[0], nums[1] is zero. -/
theorem spec_6 (nums : Slice Std.I64) (a b : Int)
    (h_vals : vals nums = [a, b])
    (h_a_lo : 0 ≤ a) (h_a_hi : a ≤ 100) (h_b_lo : 0 ≤ b) (h_b_hi : b ≤ 100)
    (h_zero : a = 0 ∨ b = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    (a = 0 ∧ b = 0 → r.val = 4) ∧
    (a + b = 1 → r.val = 1) ∧
    (2 ≤ a + b → r.val = 0) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b : Int)
    (h_vals : vals nums = [a, b])
    (h_a_lo : 0 ≤ a) (h_a_hi : a ≤ 100) (h_b_lo : 0 ≤ b) (h_b_hi : b ≤ 100)
    (h_zero : a = 0 ∨ b = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), (a = 0 ∧ b = 0 → r.val = 4) ∧
    (a + b = 1 → r.val = 1) ∧
    (2 ≤ a + b → r.val = 0)) := by
  sorry

/-- Whenever the function returns a result r, r > 0 holds if and only if there exists an index i with 0 <= i < n and nums[i] = 0 such that |L(i) - R(i)| <= 1, where L(i) = sum_{0 <= j < i} nums[j] and R(i) = sum_{i < j < n} nums[j].
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_7 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    (r.val > 0 ↔ ∃ i, i < (vals nums).length ∧ (vals nums)[i]? = some (0 : Int) ∧
      (leftSum (vals nums) i - rightSum (vals nums) i).natAbs ≤ 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), (r.val > 0 ↔ ∃ i, i < (vals nums).length ∧ (vals nums)[i]? = some (0 : Int) ∧
      (leftSum (vals nums) i - rightSum (vals nums) i).natAbs ≤ 1)) := by
  sorry

/-- Whenever the function returns a result r, r = 2*z0, where z0 is the number of indices i with 0 <= i < n, nums[i] = 0, and L(i) = R(i), with L(i) = sum_{0 <= j < i} nums[j] and R(i) = sum_{i < j < n} nums[j].
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; there exists an index i with nums[i] = 0; and S = sum_{i=0}^{n-1} nums[i] is even. -/
theorem spec_8 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_even : (vals nums).sum % 2 = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    r.val = 2 * (balancedZeroCount (vals nums) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_even : (vals nums).sum % 2 = 0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), r.val = 2 * (balancedZeroCount (vals nums) : Int)) := by
  sorry

/-- Whenever the function returns a result r, r = z1, where z1 is the number of indices i with 0 <= i < n, nums[i] = 0, and |L(i) - R(i)| = 1, with L(i) = sum_{0 <= j < i} nums[j] and R(i) = sum_{i < j < n} nums[j].
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; there exists an index i with nums[i] = 0; and S = sum_{i=0}^{n-1} nums[i] is odd. -/
theorem spec_9 (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_odd : (vals nums).sum % 2 = 1)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    r.val = (adjacentZeroCount (vals nums) : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_odd : (vals nums).sum % 2 = 1)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), r.val = (adjacentZeroCount (vals nums) : Int)) := by
  sorry

/-- Let rev be the slice of length n defined by rev[j] = nums[n - 1 - j] for 0 <= j < n. Whenever the function returns r on nums and returns r_rev on rev, r = r_rev.
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_10 (nums rev : Slice Std.I64) (r r_rev : Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_rev : rev.val = nums.val.reverse)
    (h_run : count_valid_selections nums = ok r)
    (h_run_rev : count_valid_selections rev = ok r_rev) :
    r.val = r_rev.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums rev : Slice Std.I64) (r r_rev : Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_rev : rev.val = nums.val.reverse)
    (h_run : count_valid_selections nums = ok r)
    (h_run_rev : count_valid_selections rev = ok r_rev), r.val = r_rev.val) := by
  sorry

/-- Let S = sum_{j=0}^{n-1} nums[j]. Whenever the function returns r on nums and returns r_t on t, r_t = r + e, where e = 2 if S = 0, e = 1 if S = 1, and e = 0 if S >= 2.
  Preconditions: Let n = len(nums). The input satisfies n <= 99, 1 <= n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there exists an index i with 0 <= i < n such that nums[i] = 0. Let t be the slice of length n + 1 with t[j] = nums[j] for 0 <= j < n and t[n] = 0. -/
theorem spec_11 (nums t : Slice Std.I64) (z : Std.I64) (r r_t : Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 99)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_z : z.val = 0)
    (h_t : t.val = nums.val ++ [z])
    (h_run : count_valid_selections nums = ok r)
    (h_run_t : count_valid_selections t = ok r_t) :
    ((vals nums).sum = 0 → r_t.val = r.val + 2) ∧
    ((vals nums).sum = 1 → r_t.val = r.val + 1) ∧
    (2 ≤ (vals nums).sum → r_t.val = r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums t : Slice Std.I64) (z : Std.I64) (r r_t : Std.I64)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 99)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_zero : ∃ x ∈ vals nums, x = 0)
    (h_z : z.val = 0)
    (h_t : t.val = nums.val ++ [z])
    (h_run : count_valid_selections nums = ok r)
    (h_run_t : count_valid_selections t = ok r_t), ((vals nums).sum = 0 → r_t.val = r.val + 2) ∧
    ((vals nums).sum = 1 → r_t.val = r.val + 1) ∧
    (2 ≤ (vals nums).sum → r_t.val = r.val)) := by
  sorry

/-- Let i0 be the unique index with nums[i0] = 0, L = sum_{0 <= j < i0} nums[j], and R = sum_{i0 < j < n} nums[j]. Whenever the function returns a result r, r = 2 if L = R, r = 1 if |L - R| = 1, and r = 0 otherwise.
  Preconditions: Let n = len(nums). The input satisfies n >= 1, n <= 100; for every index i with 0 <= i < n, 0 <= nums[i] <= 100; and there is exactly one index i with 0 <= i < n such that nums[i] = 0. -/
theorem spec_12 (nums : Slice Std.I64) (i0 : Nat)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_i0_lt : i0 < (vals nums).length)
    (h_i0_zero : (vals nums)[i0]? = some (0 : Int))
    (h_unique : ∀ j, j < (vals nums).length → (vals nums)[j]? = some (0 : Int) → j = i0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r) :
    (leftSum (vals nums) i0 = rightSum (vals nums) i0 → r.val = 2) ∧
    ((leftSum (vals nums) i0 - rightSum (vals nums) i0).natAbs = 1 → r.val = 1) ∧
    (leftSum (vals nums) i0 ≠ rightSum (vals nums) i0 →
      (leftSum (vals nums) i0 - rightSum (vals nums) i0).natAbs ≠ 1 → r.val = 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (i0 : Nat)
    (h_n_pos : 1 ≤ nums.val.length) (h_n_le : nums.val.length ≤ 100)
    (h_bounds : ∀ x ∈ vals nums, 0 ≤ x ∧ x ≤ 100)
    (h_i0_lt : i0 < (vals nums).length)
    (h_i0_zero : (vals nums)[i0]? = some (0 : Int))
    (h_unique : ∀ j, j < (vals nums).length → (vals nums)[j]? = some (0 : Int) → j = i0)
    (r : Std.I64) (h_run : count_valid_selections nums = ok r), (leftSum (vals nums) i0 = rightSum (vals nums) i0 → r.val = 2) ∧
    ((leftSum (vals nums) i0 - rightSum (vals nums) i0).natAbs = 1 → r.val = 1) ∧
    (leftSum (vals nums) i0 ≠ rightSum (vals nums) i0 →
      (leftSum (vals nums) i0 - rightSum (vals nums) i0).natAbs ≠ 1 → r.val = 0)) := by
  sorry

end AegisSpec.CountValidSelections
