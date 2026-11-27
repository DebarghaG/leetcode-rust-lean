import Aegis.SearchInsert.Code.Funs

/-!
# Specifications of `Aegis.SearchInsert.search_insert`

LeetCode problem `search-insert-position`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SearchInsert

def valuesInBounds (nums : Slice I64) : Prop :=
  ∀ (i : Nat) (hi : i < nums.val.length),
    -10000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 10000

def strictlySorted (nums : Slice I64) : Prop :=
  ∀ (i j : Nat) (hij : i < j) (hj : j < nums.val.length),
    (nums.val[i]).val < (nums.val[j]).val

def countLt (nums : Slice I64) (target : I64) : Nat :=
  (nums.val.filter (fun x => decide (x.val < target.val))).length

def occurs (nums : Slice I64) (target : I64) : Prop :=
  ∃ x ∈ nums.val, x.val = target.val

/-- The function returns a result r, and r equals the number of indices i such that 0 <= i < len(nums) and nums[i] < target.
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_1 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∃ r : I64, Aegis.SearchInsert.search_insert nums target = ok r ∧
      r.val = (countLt nums target : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∃ r : I64, Aegis.SearchInsert.search_insert nums target = ok r ∧
      r.val = (countLt nums target : Int)) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= len(nums).
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_2 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < r, nums[i] < target.
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_3 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), (i : Int) < r.val →
        (nums.val[i]).val < target.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), (i : Int) < r.val →
        (nums.val[i]).val < target.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with r <= i < len(nums), target <= nums[i].
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_4 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (i : Int) →
        target.val ≤ (nums.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (i : Int) →
        target.val ≤ (nums.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r, if there exists an index k with 0 <= k < len(nums) and nums[k] = target, then r = k.
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_5 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (k : Nat) (hk : k < nums.val.length), (nums.val[k]).val = target.val →
        r.val = (k : Int) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (k : Nat) (hk : k < nums.val.length), (nums.val[k]).val = target.val →
        r.val = (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, if target does not occur in nums, then for every i with 0 <= i < r, nums[i] < target, and for every i with r <= i < len(nums), target < nums[i].
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_6 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r → ¬ occurs nums target →
      (∀ (i : Nat) (hi : i < nums.val.length), (i : Int) < r.val →
        (nums.val[i]).val < target.val) ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (i : Int) →
        target.val < (nums.val[i]).val) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r → ¬ occurs nums target →
      (∀ (i : Nat) (hi : i < nums.val.length), (i : Int) < r.val →
        (nums.val[i]).val < target.val) ∧
      (∀ (i : Nat) (hi : i < nums.val.length), r.val ≤ (i : Int) →
        target.val < (nums.val[i]).val)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if target <= nums[i], then r <= i.
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_7 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), target.val ≤ (nums.val[i]).val →
        r.val ≤ (i : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), target.val ≤ (nums.val[i]).val →
        r.val ≤ (i : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if nums[i] < target, then i < r.
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_8 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val < target.val →
        (i : Int) < r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∀ r : I64, Aegis.SearchInsert.search_insert nums target = ok r →
      ∀ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val < target.val →
        (i : Int) < r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail due to overflow, out-of-bounds access, or panic).
  Preconditions: Let n = len(nums). Preconditions: 1 <= n <= 10000; for every i with 0 <= i < n, -10000 <= nums[i] <= 10000; for every i, j with 0 <= i < j < n, nums[i] < nums[j]; -10000 <= target <= 10000. -/
theorem spec_9 (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000) :
    ∃ r : I64, Aegis.SearchInsert.search_insert nums target = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 10000)
    (h_values : valuesInBounds nums) (h_sorted : strictlySorted nums)
    (h_target : -10000 ≤ target.val ∧ target.val ≤ 10000), ∃ r : I64, Aegis.SearchInsert.search_insert nums target = ok r) := by
  sorry

end AegisSpec.SearchInsert
