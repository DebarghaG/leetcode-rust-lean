import Aegis.SubarraySum.Code.Funs

/-!
# Specifications of `Aegis.SubarraySum.subarray_sum`

LeetCode problem `sum-of-variable-length-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SubarraySum

def intVals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (i : ℕ) : ℤ := (intVals nums).getD i 0

def rangeSum (nums : Slice Std.I64) (lo hi : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc lo hi, elem nums j

def startIdx (nums : Slice Std.I64) (i : ℕ) : ℕ := (max 0 ((i : ℤ) - elem nums i)).toNat

def seg (nums : Slice Std.I64) (i : ℕ) : ℤ := rangeSum nums (startIdx nums i) i

def coverCount (nums : Slice Std.I64) (n j : ℕ) : ℕ :=
  ((Finset.range n).filter (fun i => startIdx nums i ≤ j ∧ j ≤ i)).card

/-- The function returns a result r, and r = sum_{i=0}^{n-1} T_i = sum_{i=0}^{n-1} sum_{j=max(0, i - nums[i])}^{i} nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. For each i, set start_i = max(0, i - nums[i]) and T_i = sum_{j=start_i}^{i} nums[j]. -/
theorem spec_1 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ i ∈ Finset.range n, seg nums i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ i ∈ Finset.range n, seg nums i) := by
  sorry

/-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. For each i, set start_i = max(0, i - nums[i]) and T_i = sum_{j=start_i}^{i} nums[j]. -/
theorem spec_2 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r) := by
  sorry

/-- The function returns a result r, and sum_{i=0}^{n-1} nums[i] <= r <= n * sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. For each i, set start_i = max(0, i - nums[i]) and T_i = sum_{j=start_i}^{i} nums[j]. -/
theorem spec_3 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      rangeSum nums 0 (n - 1) ≤ r.val ∧
      r.val ≤ (n : ℤ) * rangeSum nums 0 (n - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      rangeSum nums 0 (n - 1) ≤ r.val ∧
      r.val ≤ (n : ℤ) * rangeSum nums 0 (n - 1)) := by
  sorry

/-- Whenever the function returns r_a for a and r_b for b, we have r_a < r_b.
  Preconditions: Let n = len(a) = len(b). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= a[i] <= b[i] <= 1000. Also assume a != b. -/
theorem spec_4 (a b : Slice Std.I64) (n : ℕ)
    (hna : n = (Slice.len a).val) (hnb : n = (Slice.len b).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem a i ∧ elem a i ≤ elem b i ∧ elem b i ≤ 1000)
    (hne : a ≠ b) :
    ∀ r_a r_b, Aegis.SubarraySum.subarray_sum a = ok r_a →
      Aegis.SubarraySum.subarray_sum b = ok r_b → r_a.val < r_b.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (a b : Slice Std.I64) (n : ℕ)
    (hna : n = (Slice.len a).val) (hnb : n = (Slice.len b).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem a i ∧ elem a i ≤ elem b i ∧ elem b i ≤ 1000)
    (hne : a ≠ b), ∀ r_a r_b, Aegis.SubarraySum.subarray_sum a = ok r_a →
      Aegis.SubarraySum.subarray_sum b = ok r_b → r_a.val < r_b.val) := by
  sorry

/-- If nums[i] = 1 for every i with 0 <= i < n, then the function returns r = 2 * n - 1.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. In addition, for every i with 0 <= i < n, nums[i] = 1. -/
theorem spec_5 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
    (hone : ∀ i : ℕ, i < n → elem nums i = 1) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧ r.val = 2 * (n : ℤ) - 1 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
    (hone : ∀ i : ℕ, i < n → elem nums i = 1), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧ r.val = 2 * (n : ℤ) - 1) := by
  sorry

/-- If nums[i] >= i for every i with 0 <= i < n, then the function returns r = sum_{j=0}^{n-1} (n - j) * nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. In addition, for every i with 0 <= i < n, nums[i] >= i. -/
theorem spec_6 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
    (hge : ∀ i : ℕ, i < n → (i : ℤ) ≤ elem nums i) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ j ∈ Finset.range n, ((n : ℤ) - (j : ℤ)) * elem nums j := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000)
    (hge : ∀ i : ℕ, i < n → (i : ℤ) ≤ elem nums i), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ j ∈ Finset.range n, ((n : ℤ) - (j : ℤ)) * elem nums j) := by
  sorry

/-- The function returns r = sum_{j=0}^{n-1} nums[j] * c_j, where c_j is the number of indices i with 0 <= i < n such that max(0, i - nums[i]) <= j <= i.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 1000. For each i, set start_i = max(0, i - nums[i]) and T_i = sum_{j=start_i}^{i} nums[j]. -/
theorem spec_7 (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000) :
    ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ j ∈ Finset.range n, elem nums j * (coverCount nums n j : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (hn : n = (Slice.len nums).val)
    (hpos : 1 ≤ n) (hle : n ≤ 100)
    (hval : ∀ i : ℕ, i < n → 1 ≤ elem nums i ∧ elem nums i ≤ 1000), ∃ r, Aegis.SubarraySum.subarray_sum nums = ok r ∧
      r.val = ∑ j ∈ Finset.range n, elem nums j * (coverCount nums n j : ℤ)) := by
  sorry

end AegisSpec.SubarraySum
