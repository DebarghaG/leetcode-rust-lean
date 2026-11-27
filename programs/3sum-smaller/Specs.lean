import Aegis.ThreeSumSmaller.Code.Funs

/-!
# Specifications of `Aegis.ThreeSumSmaller.three_sum_smaller`

LeetCode problem `3sum-smaller`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.ThreeSumSmaller

namespace AegisSpec.ThreeSumSmaller

def choose3 (n : ℕ) : ℕ := n * (n - 1) * (n - 2) / 6

def tripleCount (l : List I64) (t : ℤ) : ℕ :=
  (((Finset.range l.length).product
      ((Finset.range l.length).product (Finset.range l.length))).filter
    (fun p => p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
      (l[p.1]!).val + (l[p.2.1]!).val + (l[p.2.2]!).val < t)).card

def IsPermOf (l l' : List I64) : Prop :=
  ∃ p : Fin l.length ≃ Fin l.length,
    l' = (List.finRange l.length).map (fun i => l.get (p i))

/-- three_sum_smaller nums target returns a result r (not an error), and r equals the number of index triples (i,j,k) such that 0 <= i < j < k < len(nums) and nums[i] + nums[j] + nums[k] < target, where the sum is taken over the mathematical integers. Equivalently, r = |{(i,j,k) : 0 <= i < j < k < len(nums) and nums[i] + nums[j] + nums[k] < target}|.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_1 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (tripleCount nums.val target.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100), ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (tripleCount nums.val target.val : ℤ)) := by
  sorry

/-- three_sum_smaller nums target does not fail: it returns a result r rather than an error, overflow, or panic.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_2 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100) :
    ∃ r, three_sum_smaller nums target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100), ∃ r, three_sum_smaller nums target = ok r) := by
  sorry

/-- Let n = len(nums). three_sum_smaller nums target returns a result r and 0 <= r <= C(n,3), where C(n,3) is the total number of index triples 0 <= i < j < k < n, so C(n,3) = 0 when n < 3.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_3 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (choose3 nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100), ∃ r, three_sum_smaller nums target = ok r ∧
      0 ≤ r.val ∧ r.val ≤ (choose3 nums.val.length : ℤ)) := by
  sorry

/-- If len(nums) < 3, then three_sum_smaller nums target returns a result r and r = 0.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_4 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hshort : nums.val.length < 3) :
    ∃ r, three_sum_smaller nums target = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hshort : nums.val.length < 3), ∃ r, three_sum_smaller nums target = ok r ∧ r.val = 0) := by
  sorry

/-- If len(nums) = 3, then three_sum_smaller nums target returns a result r and r = 1 if nums[0] + nums[1] + nums[2] < target, and r = 0 otherwise.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_5 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hthree : nums.val.length = 3) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (if (nums.val[0]!).val + (nums.val[1]!).val + (nums.val[2]!).val < target.val
        then 1 else 0) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hthree : nums.val.length = 3), ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (if (nums.val[0]!).val + (nums.val[1]!).val + (nums.val[2]!).val < target.val
        then 1 else 0)) := by
  sorry

/-- If for every 0 <= i < j < k < len(nums) we have nums[i] + nums[j] + nums[k] < target, then three_sum_smaller nums target returns a result r and r = C(len(nums),3), the total number of index triples, with C(n,3) = 0 when n < 3.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_6 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hall : ∀ i j k : ℕ, i < j → j < k → k < nums.val.length →
      (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val < target.val) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (choose3 nums.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hall : ∀ i j k : ℕ, i < j → j < k → k < nums.val.length →
      (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val < target.val), ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (choose3 nums.val.length : ℤ)) := by
  sorry

/-- If for every 0 <= i < j < k < len(nums) we have nums[i] + nums[j] + nums[k] >= target, then three_sum_smaller nums target returns a result r and r = 0.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_7 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hall : ∀ i j k : ℕ, i < j → j < k → k < nums.val.length →
      target.val ≤ (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val) :
    ∃ r, three_sum_smaller nums target = ok r ∧ r.val = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hall : ∀ i j k : ℕ, i < j → j < k → k < nums.val.length →
      target.val ≤ (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val), ∃ r, three_sum_smaller nums target = ok r ∧ r.val = 0) := by
  sorry

/-- three_sum_smaller nums target returns a result r and r > 0 if and only if there exist indices i, j, k with 0 <= i < j < k < len(nums) and nums[i] + nums[j] + nums[k] < target.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_8 (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      (0 < r.val ↔ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < nums.val.length ∧
        (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val < target.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100), ∃ r, three_sum_smaller nums target = ok r ∧
      (0 < r.val ↔ ∃ i j k : ℕ, i < j ∧ j < k ∧ k < nums.val.length ∧
        (nums.val[i]!).val + (nums.val[j]!).val + (nums.val[k]!).val < target.val)) := by
  sorry

/-- For every slice nums' that is a permutation of nums, meaning len(nums') = len(nums) and there exists a bijection p on {0,...,len(nums)-1} with nums'[i] = nums[p(i)] for every i, three_sum_smaller nums target and three_sum_smaller nums' target both return results r and r', and r = r'.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_9 (nums nums' : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hperm : IsPermOf nums.val nums'.val) :
    ∃ r r', three_sum_smaller nums target = ok r ∧
      three_sum_smaller nums' target = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64) (target : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hperm : IsPermOf nums.val nums'.val), ∃ r r', three_sum_smaller nums target = ok r ∧
      three_sum_smaller nums' target = ok r' ∧ r.val = r'.val) := by
  sorry

/-- For any integers t1 and t2 with -100 <= t1 <= t2 <= 100, if three_sum_smaller nums t1 returns r1 and three_sum_smaller nums t2 returns r2, then r1 <= r2.
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_10 (nums : Slice I64) (t1 t2 : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (ht1 : -100 ≤ t1.val) (hle : t1.val ≤ t2.val) (ht2 : t2.val ≤ 100)
    (r1 r2 : I64)
    (h1 : three_sum_smaller nums t1 = ok r1)
    (h2 : three_sum_smaller nums t2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (t1 t2 : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (ht1 : -100 ≤ t1.val) (hle : t1.val ≤ t2.val) (ht2 : t2.val ≤ 100)
    (r1 r2 : I64)
    (h1 : three_sum_smaller nums t1 = ok r1)
    (h2 : three_sum_smaller nums t2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If there is an integer v such that nums[i] = v for every 0 <= i < len(nums), then three_sum_smaller nums target returns a result r and r = C(len(nums),3) if 3*v < target, and r = 0 otherwise, where C(n,3) is the total number of index triples (with C(n,3) = 0 when n < 3).
  Preconditions: Let n = len(nums). Then 0 <= n <= 3500; for every i with 0 <= i < n, -100 <= nums[i] <= 100; and -100 <= target <= 100. -/
theorem spec_11 (nums : Slice I64) (target v : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hconst : ∀ x ∈ nums.val, x.val = v.val) :
    ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (if 3 * v.val < target.val then (choose3 nums.val.length : ℤ) else 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (target v : I64)
    (hlen : nums.val.length ≤ 3500)
    (helem : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (htarget : -100 ≤ target.val ∧ target.val ≤ 100)
    (hconst : ∀ x ∈ nums.val, x.val = v.val), ∃ r, three_sum_smaller nums target = ok r ∧
      r.val = (if 3 * v.val < target.val then (choose3 nums.val.length : ℤ) else 0)) := by
  sorry

end AegisSpec.ThreeSumSmaller
