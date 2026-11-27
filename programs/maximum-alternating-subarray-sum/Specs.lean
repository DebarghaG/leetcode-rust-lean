import Aegis.MaximumAlternatingSubarraySum.Code.Funs

/-!
# Specifications of `Aegis.MaximumAlternatingSubarraySum.maximum_alternating_subarray_sum`

LeetCode problem `maximum-alternating-subarray-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaximumAlternatingSubarraySum

open Aegis.MaximumAlternatingSubarraySum (maximum_alternating_subarray_sum)

def altSum : List ℤ → ℤ
  | [] => 0
  | a :: rest => a - altSum rest

def altSubarraySum (l : List ℤ) (i j : ℕ) : ℤ := altSum ((l.drop i).take (j + 1 - i))

def contents (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def ElemBounds (nums : Slice Std.I64) : Prop :=
  ∀ (i : ℕ) (h : i < nums.val.length), -100000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100000

def IsAltMax (l : List ℤ) (r : ℤ) : Prop :=
  (∃ i j : ℕ, i ≤ j ∧ j < l.length ∧ altSubarraySum l i j = r) ∧
    ∀ i j : ℕ, i ≤ j → j < l.length → altSubarraySum l i j ≤ r

def IsAltMin (l : List ℤ) (m : ℤ) : Prop :=
  (∃ i j : ℕ, i ≤ j ∧ j < l.length ∧ altSubarraySum l i j = m) ∧
    ∀ i j : ℕ, i ≤ j → j < l.length → m ≤ altSubarraySum l i j

/-- The function returns a result r and r = max{ A(i,j) | 0 <= i <= j < n }, where A(i,j) = sum_{k=i}^{j} (-1)^(k-i) * nums[k] = nums[i] - nums[i+1] + nums[i+2] - ... +/ - nums[j]. The maximum is over all non-empty contiguous subarrays; subarrays of length 1 are included.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      IsAltMax (contents nums) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      IsAltMax (contents nums) r.val) := by
  sorry

/-- The function returns a result r (it does not fail, overflow, go out of bounds, or panic) and |r| <= 100000 * n <= 10^10. Hence r is always representable as an I64.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      |r.val| ≤ 100000 * (n : ℤ) ∧ 100000 * (n : ℤ) ≤ 10 ^ 10 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      |r.val| ≤ 100000 * (n : ℤ) ∧ 100000 * (n : ℤ) ≤ 10 ^ 10) := by
  sorry

/-- The function returns a result r and, for every pair of indices i,j with 0 <= i <= j < n, A(i,j) <= r, where A(i,j) = sum_{k=i}^{j} (-1)^(k-i) * nums[k].
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      ∀ i j : ℕ, i ≤ j → j < n → altSubarraySum (contents nums) i j ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      ∀ i j : ℕ, i ≤ j → j < n → altSubarraySum (contents nums) i j ≤ r.val) := by
  sorry

/-- The function returns a result r and there exist indices i,j with 0 <= i <= j < n such that r = A(i,j), where A(i,j) = sum_{k=i}^{j} (-1)^(k-i) * nums[k].
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      ∃ i j : ℕ, i ≤ j ∧ j < n ∧ r.val = altSubarraySum (contents nums) i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      ∃ i j : ℕ, i ≤ j ∧ j < n ∧ r.val = altSubarraySum (contents nums) i j) := by
  sorry

/-- The function returns a result r and |r| <= sum_{i=0}^{n-1} |nums[i]|.
  Preconditions: n = len(nums); 1 <= n <= 100000; for every i with 0 <= i < n, -100000 <= nums[i] <= 100000. -/
theorem spec_5 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      |r.val| ≤ ((contents nums).map (fun x => |x|)).sum := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      |r.val| ≤ ((contents nums).map (fun x => |x|)).sum) := by
  sorry

/-- The function returns a result r and r = nums[0].
  Preconditions: n = len(nums); n = 1; -100000 <= nums[0] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn1 : n = 1)
    (hb0 : -100000 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 100000) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = (nums.val[0]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn1 : n = 1)
    (hb0 : -100000 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 100000), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = (nums.val[0]).val) := by
  sorry

/-- The function returns a result r and r = max(nums[0], nums[1], nums[0] - nums[1]), where max denotes the largest of the three integers.
  Preconditions: n = len(nums); n = 2; -100000 <= nums[0] <= 100000; -100000 <= nums[1] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn2 : n = 2)
    (hb0 : -100000 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 100000)
    (hb1 : -100000 ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ 100000) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = max (nums.val[0]).val (max (nums.val[1]).val
        ((nums.val[0]).val - (nums.val[1]).val)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ)
    (hn : n = nums.val.length) (hn2 : n = 2)
    (hb0 : -100000 ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ 100000)
    (hb1 : -100000 ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ 100000), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = max (nums.val[0]).val (max (nums.val[1]).val
        ((nums.val[0]).val - (nums.val[1]).val))) := by
  sorry

/-- The function returns a result r and r = max(c, 0).
  Preconditions: n = len(nums); 2 <= n <= 100000; there exists an integer c with -100000 <= c <= 100000 such that for every i with 0 <= i < n, nums[i] = c. -/
theorem spec_8 (nums : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = nums.val.length) (hn_lo : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hc : -100000 ≤ c ∧ c ≤ 100000)
    (hconst : ∀ (i : ℕ) (h : i < n), (nums.val[i]).val = c) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = max c 0 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = nums.val.length) (hn_lo : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hc : -100000 ≤ c ∧ c ≤ 100000)
    (hconst : ∀ (i : ℕ) (h : i < n), (nums.val[i]).val = c), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      r.val = max c 0) := by
  sorry

/-- The function returns a result r on nums and a result r' on nums', and r <= r'.
  Preconditions: Let nums be a slice satisfying n = len(nums), 1 <= n <= 100000, and -100000 <= nums[i] <= 100000 for every 0 <= i < n. Let nums' be a slice satisfying m = len(nums'), 1 <= m <= 100000, and -100000 <= nums'[i] <= 100000 for every 0 <= i < m. Assume nums is a contiguous subarray of nums': there exists d with 0 <= d and d + n <= m and nums'[d+i] = nums[i] for every 0 <= i < n. -/
theorem spec_9 (nums nums' : Slice Std.I64) (n m d : ℕ)
    (hn : n = nums.val.length) (hm : m = nums'.val.length)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000) (hm_pos : 1 ≤ m) (hm_ub : m ≤ 100000)
    (hb : ElemBounds nums) (hb' : ElemBounds nums')
    (hd : d + n ≤ m)
    (hsub : ∀ (i : ℕ) (h : i < n), (nums'.val[d + i]).val = (nums.val[i]).val) :
    ∃ r r' : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      maximum_alternating_subarray_sum nums' = ok r' ∧ r.val ≤ r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n m d : ℕ)
    (hn : n = nums.val.length) (hm : m = nums'.val.length)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000) (hm_pos : 1 ≤ m) (hm_ub : m ≤ 100000)
    (hb : ElemBounds nums) (hb' : ElemBounds nums')
    (hd : d + n ≤ m)
    (hsub : ∀ (i : ℕ) (h : i < n), (nums'.val[d + i]).val = (nums.val[i]).val), ∃ r r' : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      maximum_alternating_subarray_sum nums' = ok r' ∧ r.val ≤ r'.val) := by
  sorry

/-- Let m = min{ A(i,j) | 0 <= i <= j < n }, where A(i,j) = sum_{k=i}^{j} (-1)^(k-i) * nums[k]. The function returns a result r' on nums' and r' = -m.
  Preconditions: Let nums be a slice satisfying n = len(nums), 1 <= n <= 100000, and -100000 <= nums[i] <= 100000 for every 0 <= i < n. Let nums' be any slice with len(nums') = n and nums'[i] = -nums[i] for every 0 <= i < n. -/
theorem spec_10 (nums nums' : Slice Std.I64) (n : ℕ) (m : ℤ)
    (hn : n = nums.val.length) (hn' : nums'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums)
    (hm : IsAltMin (contents nums) m)
    (hneg : ∀ (i : ℕ) (h : i < n), (nums'.val[i]).val = -((nums.val[i]).val)) :
    ∃ r' : Std.I64, maximum_alternating_subarray_sum nums' = ok r' ∧ r'.val = -m := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (n : ℕ) (m : ℤ)
    (hn : n = nums.val.length) (hn' : nums'.val.length = n)
    (hn_pos : 1 ≤ n) (hn_ub : n ≤ 100000)
    (hb : ElemBounds nums)
    (hm : IsAltMin (contents nums) m)
    (hneg : ∀ (i : ℕ) (h : i < n), (nums'.val[i]).val = -((nums.val[i]).val)), ∃ r' : Std.I64, maximum_alternating_subarray_sum nums' = ok r' ∧ r'.val = -m) := by
  sorry

/-- The function returns a result r and, if c >= 0 then r = c * n, while if c < 0 then r = -c * (n - 1).
  Preconditions: n = len(nums); 2 <= n <= 100000; there exists an integer c with -100000 <= c <= 100000 such that for every k with 0 <= k < n, nums[k] = c when k is even and nums[k] = -c when k is odd. -/
theorem spec_11 (nums : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = nums.val.length) (hn_lo : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hc : -100000 ≤ c ∧ c ≤ 100000)
    (halt : ∀ (i : ℕ) (h : i < n), (nums.val[i]).val = (if i % 2 = 0 then c else -c)) :
    ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      (0 ≤ c → r.val = c * (n : ℤ)) ∧
      (c < 0 → r.val = -(c * ((n : ℤ) - 1))) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (n : ℕ) (c : ℤ)
    (hn : n = nums.val.length) (hn_lo : 2 ≤ n) (hn_ub : n ≤ 100000)
    (hc : -100000 ≤ c ∧ c ≤ 100000)
    (halt : ∀ (i : ℕ) (h : i < n), (nums.val[i]).val = (if i % 2 = 0 then c else -c)), ∃ r : Std.I64, maximum_alternating_subarray_sum nums = ok r ∧
      (0 ≤ c → r.val = c * (n : ℤ)) ∧
      (c < 0 → r.val = -(c * ((n : ℤ) - 1)))) := by
  sorry

end AegisSpec.MaximumAlternatingSubarraySum
