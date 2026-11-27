import Aegis.MinStartValue.Code.Funs

/-!
# Specifications of `Aegis.MinStartValue.min_start_value`

LeetCode problem `minimum-value-to-get-positive-step-by-step-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinStartValue

  namespace AegisSpec.MinStartValue

  def elems (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def prefix_sum (nums : Slice I64) (k : ℕ) : ℤ := ((elems nums).take k).sum

  def prefix_sums (nums : Slice I64) : List ℤ := (elems nums).scanl (fun acc x => acc + x) 0

  def min_prefix_sum (nums : Slice I64) : ℤ :=
    match (prefix_sums nums).tail with
    | [] => 0
    | x :: xs => xs.foldl min x

  /-- The function returns a result r and r is the least positive integer s such that for every k with 1 <= k <= len(nums), s + (sum_{j=0}^{k-1} nums[j]) >= 1. Equivalently, r is positive, r satisfies all those prefix-sum inequalities, and every positive integer s < r violates at least one of them.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r : I64,
        min_start_value nums = ok r ∧
        0 < r.val ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ nums.val.length → 1 ≤ r.val + prefix_sum nums k) ∧
        (∀ s : ℤ, 0 < s → s < r.val →
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ s + prefix_sum nums k < 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∃ r : I64,
          min_start_value nums = ok r ∧
          0 < r.val ∧
          (∀ k : ℕ, 1 ≤ k → k ≤ nums.val.length → 1 ≤ r.val + prefix_sum nums k) ∧
          (∀ s : ℤ, 0 < s → s < r.val →
            ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ s + prefix_sum nums k < 1)) := by
    sorry

  /-- The function does not fail: it returns a result r, with no arithmetic overflow, no out-of-bounds access, and no panic.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∃ r : I64, min_start_value nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∃ r : I64, min_start_value nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 10001.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∀ r : I64, min_start_value nums = ok r → 1 ≤ r.val ∧ r.val ≤ 10001 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∀ r : I64, min_start_value nums = ok r → 1 ≤ r.val ∧ r.val ≤ 10001) := by
    sorry

  /-- Whenever the function returns a result r, let m = min { sum_{j=0}^{k-1} nums[j] | 1 <= k <= len(nums) }. Then r = max(1, 1 - m).
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∀ r : I64, min_start_value nums = ok r → r.val = max 1 (1 - min_prefix_sum nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∀ r : I64, min_start_value nums = ok r → r.val = max 1 (1 - min_prefix_sum nums)) := by
    sorry

  /-- Whenever the function returns a result r, r > 1 if and only if there exists k with 1 <= k <= len(nums) such that sum_{j=0}^{k-1} nums[j] < 0.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∀ r : I64, min_start_value nums = ok r →
        1 < r.val ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ prefix_sum nums k < 0 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∀ r : I64, min_start_value nums = ok r →
          1 < r.val ↔ ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ prefix_sum nums k < 0) := by
    sorry

  /-- Whenever the function returns a result r, if r > 1 then there exists k with 1 <= k <= len(nums) such that r + (sum_{j=0}^{k-1} nums[j]) = 1.
    Preconditions: len(nums) >= 1, len(nums) <= 100, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
      ∀ r : I64, min_start_value nums = ok r → 1 < r.val →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ r.val + prefix_sum nums k = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∀ r : I64, min_start_value nums = ok r → 1 < r.val →
          ∃ k : ℕ, 1 ≤ k ∧ k ≤ nums.val.length ∧ r.val + prefix_sum nums k = 1) := by
    sorry

  /-- Let n = len(nums). For every integer c with -100 <= c <= 100, let nums' be the slice of length n+1 whose first n elements equal nums and whose last element is c. Whenever min_start_value(nums) returns r and min_start_value(nums') returns r', we have r' >= r.
    Preconditions: len(nums) >= 1, len(nums) <= 99, and for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice I64)
      (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
      (c : I64) (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100)
      (nums' : Slice I64) (h_nums' : nums'.val = nums.val ++ [c]) :
      ∀ r r' : I64, min_start_value nums = ok r → min_start_value nums' = ok r' →
        r.val ≤ r'.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 1 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 99)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
        (c : I64) (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100)
        (nums' : Slice I64) (h_nums' : nums'.val = nums.val ++ [c]), ∀ r r' : I64, min_start_value nums = ok r → min_start_value nums' = ok r' →
          r.val ≤ r'.val) := by
    sorry

  /-- Let nums' be the slice of length len(nums)-1 obtained by deleting the last element of nums. Whenever min_start_value(nums) returns r and min_start_value(nums') returns r', we have r = r'.
    Preconditions: len(nums) >= 2, len(nums) <= 100, for every i with 0 <= i < len(nums), -100 <= nums[i] <= 100, and nums[len(nums)-1] >= 0. -/
  theorem spec_8 (nums : Slice I64)
      (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
      (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
      (last : I64) (h_last : nums.val.getLast? = some last) (h_last_nonneg : 0 ≤ last.val)
      (nums' : Slice I64) (h_nums' : nums'.val = nums.val.dropLast) :
      ∀ r r' : I64, min_start_value nums = ok r → min_start_value nums' = ok r' →
        r.val = r'.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len_ge : 2 ≤ nums.val.length) (h_len_le : nums.val.length ≤ 100)
        (h_bounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
        (last : I64) (h_last : nums.val.getLast? = some last) (h_last_nonneg : 0 ≤ last.val)
        (nums' : Slice I64) (h_nums' : nums'.val = nums.val.dropLast), ∀ r r' : I64, min_start_value nums = ok r → min_start_value nums' = ok r' →
          r.val = r'.val) := by
    sorry

  end AegisSpec.MinStartValue
