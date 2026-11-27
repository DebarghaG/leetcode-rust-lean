import Aegis.SortTransformedArray.Code.Funs

/-!
# Specifications of `Aegis.SortTransformedArray.sort_transformed_array`

LeetCode problem `sort-transformed-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SortTransformedArray

def transform (a b c : Std.I64) (x : ℤ) : ℤ := a.val * x * x + b.val * x + c.val

def sliceValues (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def vecValues (r : alloc.vec.Vec Std.I64) : List ℤ := r.val.map (fun x => x.val)

def Nondecreasing (l : List ℤ) : Prop := ∀ j : ℕ, j + 1 < l.length → l[j]! ≤ l[j+1]!

/-- Let f(x) = a*x*x + b*x + c. The function returns a result r and: (1) len(r) = n; (2) r is sorted in nondecreasing order, i.e. for every j with 0 <= j < n-1, r[j] <= r[j+1]; (3) for every integer y, the number of indices j with 0 <= j < n and r[j] = y equals the number of indices i with 0 <= i < n and f(nums[i]) = y.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_1 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      Nondecreasing (vecValues r) ∧
      ∀ y : ℤ, (vecValues r).count y = ((sliceValues nums).map (transform a b c)).count y := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      Nondecreasing (vecValues r) ∧
      ∀ y : ℤ, (vecValues r).count y = ((sliceValues nums).map (transform a b c)).count y) := by
  sorry

/-- The function returns a result r; it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_2 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r) := by
  sorry

/-- The function returns a result r and len(r) = len(nums).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_3 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length) := by
  sorry

/-- The function returns a result r and r is sorted in nondecreasing order: for every j with 0 <= j < len(r)-1, r[j] <= r[j+1].
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_4 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      Nondecreasing (vecValues r) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      Nondecreasing (vecValues r)) := by
  sorry

/-- Let f(x) = a*x*x + b*x + c. The function returns a result r and for every j with 0 <= j < len(r), there exists i with 0 <= i < n such that r[j] = f(nums[i]).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_5 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      ∀ j : ℕ, j < r.val.length →
        ∃ i : ℕ, i < nums.val.length ∧
          (r.val[j]!).val = transform a b c (nums.val[i]!).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      ∀ j : ℕ, j < r.val.length →
        ∃ i : ℕ, i < nums.val.length ∧
          (r.val[j]!).val = transform a b c (nums.val[i]!).val) := by
  sorry

/-- Let f(x) = a*x*x + b*x + c. The function returns a result r and for every i with 0 <= i < n, there exists j with 0 <= j < len(r) such that r[j] = f(nums[i]).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_6 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      ∀ i : ℕ, i < nums.val.length →
        ∃ j : ℕ, j < r.val.length ∧
          (r.val[j]!).val = transform a b c (nums.val[i]!).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      ∀ i : ℕ, i < nums.val.length →
        ∃ j : ℕ, j < r.val.length ∧
          (r.val[j]!).val = transform a b c (nums.val[i]!).val) := by
  sorry

/-- Let f(x) = a*x*x + b*x + c. The function returns a result r, len(r) = n, and r[0] is a minimum of the transformed values: for every i with 0 <= i < n, r[0] <= f(nums[i]); and there exists i with 0 <= i < n such that r[0] = f(nums[i]).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_7 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ i : ℕ, i < nums.val.length →
        (r.val[0]!).val ≤ transform a b c (nums.val[i]!).val) ∧
      ∃ i : ℕ, i < nums.val.length ∧
        (r.val[0]!).val = transform a b c (nums.val[i]!).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ i : ℕ, i < nums.val.length →
        (r.val[0]!).val ≤ transform a b c (nums.val[i]!).val) ∧
      ∃ i : ℕ, i < nums.val.length ∧
        (r.val[0]!).val = transform a b c (nums.val[i]!).val) := by
  sorry

/-- Let f(x) = a*x*x + b*x + c. The function returns a result r, len(r) = n, and r[n-1] is a maximum of the transformed values: for every i with 0 <= i < n, r[n-1] >= f(nums[i]); and there exists i with 0 <= i < n such that r[n-1] = f(nums[i]).
  Preconditions: Let n = len(nums). The input satisfies the problem constraints: 1 <= n <= 200; for every i with 0 <= i < n, -100 <= nums[i] <= 100; nums is sorted in nondecreasing order, i.e. for every i with 0 <= i < n-1, nums[i] <= nums[i+1]; and -100 <= a <= 100, -100 <= b <= 100, -100 <= c <= 100. -/
theorem spec_8 (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ i : ℕ, i < nums.val.length →
        (r.val[nums.val.length - 1]!).val ≥ transform a b c (nums.val[i]!).val) ∧
      ∃ i : ℕ, i < nums.val.length ∧
        (r.val[nums.val.length - 1]!).val = transform a b c (nums.val[i]!).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (a b c : Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_max : nums.val.length ≤ 200)
    (h_nums_bound : ∀ i : ℕ,
      i < nums.val.length → -100 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 100)
    (h_nums_sorted : Nondecreasing (sliceValues nums))
    (ha_lo : -100 ≤ a.val) (ha_hi : a.val ≤ 100)
    (hb_lo : -100 ≤ b.val) (hb_hi : b.val ≤ 100)
    (hc_lo : -100 ≤ c.val) (hc_hi : c.val ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.SortTransformedArray.sort_transformed_array nums a b c = ok r ∧
      r.val.length = nums.val.length ∧
      (∀ i : ℕ, i < nums.val.length →
        (r.val[nums.val.length - 1]!).val ≥ transform a b c (nums.val[i]!).val) ∧
      ∃ i : ℕ, i < nums.val.length ∧
        (r.val[nums.val.length - 1]!).val = transform a b c (nums.val[i]!).val) := by
  sorry

end AegisSpec.SortTransformedArray
