import Aegis.MinimumOperations.Code.Funs

/-!
# Specifications of `Aegis.MinimumOperations.minimum_operations`

LeetCode problem `minimum-number-of-operations-to-make-elements-in-array-distinct`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumOperations

  def elem (nums : Slice Std.I64) (i : Int) : Int :=
    match nums.val[i.toNat]? with
    | some x => x.val
    | none => 0

  def DistinctFrom (nums : Slice Std.I64) (s : Int) : Prop :=
    ∀ i j : Int, s ≤ i → i < j → j < (nums.val.length : Int) → elem nums i ≠ elem nums j

  def PairwiseDistinct (nums : Slice Std.I64) : Prop :=
    DistinctFrom nums 0

  def IsLeastOpCount (nums : Slice Std.I64) (n : Nat) (r : Int) : Prop :=
    ∃ k : Nat, r = (k : Int) ∧ DistinctFrom nums (min (3 * (k : Int)) (n : Int)) ∧
      ∀ k' : Nat, DistinctFrom nums (min (3 * (k' : Int)) (n : Int)) → k ≤ k'

  def IsLeastDistinctStart (nums : Slice Std.I64) (t : Nat) : Prop :=
    DistinctFrom nums (t : Int) ∧ ∀ t' : Nat, t' < t → ¬ DistinctFrom nums (t' : Int)

  def IsLastRepeatIndex (nums : Slice Std.I64) (m : Nat) : Prop :=
    (∃ j : Nat, m < j ∧ j < nums.val.length ∧ elem nums (m : Int) = elem nums (j : Int)) ∧
      ∀ m' : Nat, m < m' → m' < nums.val.length →
        ¬ ∃ j : Nat, m' < j ∧ j < nums.val.length ∧ elem nums (m' : Int) = elem nums (j : Int)

  def remaining (n : Int) (r : Int) : Int :=
    n - min (3 * r) n

  /-- Whenever the function returns a result r, r is the least integer k >= 0 such that the suffix nums[min(3*k, n) .. n-1] has pairwise distinct elements: for all i and j with min(3*k, n) <= i < j < n, nums[i] != nums[j]. Equivalently, r is the minimum number of operations (each operation removes 3 elements from the front, or all remaining elements if fewer than 3 remain) after which the remaining array has pairwise distinct elements.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        IsLeastOpCount nums n r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          IsLeastOpCount nums n r.val) := by
    sorry

  /-- Whenever the function returns r, 0 <= r <= ceil(n/3), where ceil(n/3) is the integer (n+2) div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        0 ≤ r.val ∧ r.val ≤ ((n + 2) / 3 : Nat) := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          0 ≤ r.val ∧ r.val ≤ ((n + 2) / 3 : Nat)) := by
    sorry

  /-- Whenever the function returns r, r = 0 if and only if the original array nums has pairwise distinct elements, i.e. for all i and j with 0 <= i < j < n, nums[i] != nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (r.val = 0 ↔ PairwiseDistinct nums) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (r.val = 0 ↔ PairwiseDistinct nums)) := by
    sorry

  /-- Whenever the function returns r, if nums has pairwise distinct elements then r = 0; otherwise r = 1.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 4, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 4)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (PairwiseDistinct nums → r.val = 0) ∧ (¬ PairwiseDistinct nums → r.val = 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 4)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (PairwiseDistinct nums → r.val = 0) ∧ (¬ PairwiseDistinct nums → r.val = 1)) := by
    sorry

  /-- Whenever the function returns r, the array remaining after r operations is distinct: with s = min(3*r, n), for all i and j with s <= i < j < n, nums[i] != nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        DistinctFrom nums (min (3 * r.val) (n : Int)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          DistinctFrom nums (min (3 * r.val) (n : Int))) := by
    sorry

  /-- Whenever the function returns r and r > 0, the array remaining after r-1 operations is not distinct: with s = min(3*(r-1), n), there exist indices i and j such that s <= i < j < n and nums[i] = nums[j].
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r → 0 < r.val →
        ∃ i j : Int, min (3 * (r.val - 1)) (n : Int) ≤ i ∧ i < j ∧ j < (n : Int) ∧
          elem nums i = elem nums j := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r → 0 < r.val →
          ∃ i j : Int, min (3 * (r.val - 1)) (n : Int) ≤ i ∧ i < j ∧ j < (n : Int) ∧
            elem nums i = elem nums j) := by
    sorry

  /-- Whenever the function returns r, let t be the least index with 0 <= t <= n such that the suffix nums[t .. n-1] has pairwise distinct elements (for all i and j with t <= i < j < n, nums[i] != nums[j]); such a t exists, and t = n gives the empty suffix. Then r = ceil(t/3) = (t+2) div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        ∀ t : Nat, IsLeastDistinctStart nums t → r.val = ((t + 2) / 3 : Nat) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          ∀ t : Nat, IsLeastDistinctStart nums t → r.val = ((t + 2) / 3 : Nat)) := by
    sorry

  /-- Whenever the function returns r, if nums has no repeated value then r = 0. Otherwise let m be the largest index i with 0 <= i < n for which there exists j with i < j < n and nums[i] = nums[j]; then r = ceil((m+1)/3) = (m+3) div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (PairwiseDistinct nums → r.val = 0) ∧
          (¬ PairwiseDistinct nums → ∀ m : Nat, IsLastRepeatIndex nums m →
            r.val = ((m + 3) / 3 : Nat)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (PairwiseDistinct nums → r.val = 0) ∧
            (¬ PairwiseDistinct nums → ∀ m : Nat, IsLastRepeatIndex nums m →
              r.val = ((m + 3) / 3 : Nat))) := by
    sorry

  /-- Whenever the function returns r, for every integer k >= 0, the suffix nums[min(3*k, n) .. n-1] has pairwise distinct elements if and only if k >= r.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        ∀ k : Nat, (DistinctFrom nums (min (3 * (k : Int)) (n : Int)) ↔ r.val ≤ (k : Int)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          ∀ k : Nat, (DistinctFrom nums (min (3 * (k : Int)) (n : Int)) ↔ r.val ≤ (k : Int))) := by
    sorry

  /-- The function returns a result r (that is, it does not fail by panic, out-of-bounds access, or 64-bit overflow) for every input satisfying the preconditions.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∃ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∃ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r) := by
    sorry

  /-- Whenever the function returns r, the number of elements remaining after r operations is max(n - 3*r, 0); equivalently, the remaining array is empty exactly when 3*r >= n.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_11 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        remaining (n : Int) r.val = max ((n : Int) - 3 * r.val) 0 ∧
          (remaining (n : Int) r.val = 0 ↔ (n : Int) ≤ 3 * r.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          remaining (n : Int) r.val = max ((n : Int) - 3 * r.val) 0 ∧
            (remaining (n : Int) r.val = 0 ↔ (n : Int) ≤ 3 * r.val)) := by
    sorry

  /-- Whenever the function returns r on nums and returns r_tail on the suffix tail = nums[3 .. n-1] (the array of length n-3 with tail[i] = nums[i+3]), if nums has pairwise distinct elements then r = 0; otherwise r = 1 + r_tail.
    Preconditions: Let n = len(nums). Assume 4 <= n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
  theorem spec_12 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 4 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
      (tail : Slice Std.I64) (htail : tail.val = nums.val.drop 3) :
      ∀ r r_tail : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        Aegis.MinimumOperations.minimum_operations tail = ok r_tail →
        (PairwiseDistinct nums → r.val = 0) ∧
          (¬ PairwiseDistinct nums → r.val = 1 + r_tail.val) := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 4 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
        (tail : Slice Std.I64) (htail : tail.val = nums.val.drop 3), ∀ r r_tail : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          Aegis.MinimumOperations.minimum_operations tail = ok r_tail →
          (PairwiseDistinct nums → r.val = 0) ∧
            (¬ PairwiseDistinct nums → r.val = 1 + r_tail.val)) := by
    sorry

  /-- Let nums' be the array of length n+1 with nums'[i] = nums[i] for 0 <= i < n and nums'[n] = x. Whenever the function returns r on nums and returns r' on nums', r = r'.
    Preconditions: Let n = len(nums). Assume 1 <= n < 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. Let x be an integer with 1 <= x <= 100 such that x != nums[i] for every i with 0 <= i < n. -/
  theorem spec_13 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n < 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
      (x : Int) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 100)
      (hx_fresh : ∀ i : Nat, i < n → elem nums (i : Int) ≠ x)
      (nums' : Slice Std.I64) (hlen' : nums'.val.length = n + 1)
      (hprefix : ∀ i : Nat, i < n → elem nums' (i : Int) = elem nums (i : Int))
      (hlast : elem nums' (n : Int) = x) :
      ∀ r r' : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        Aegis.MinimumOperations.minimum_operations nums' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n < 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
        (x : Int) (hx_lo : 1 ≤ x) (hx_hi : x ≤ 100)
        (hx_fresh : ∀ i : Nat, i < n → elem nums (i : Int) ≠ x)
        (nums' : Slice Std.I64) (hlen' : nums'.val.length = n + 1)
        (hprefix : ∀ i : Nat, i < n → elem nums' (i : Int) = elem nums (i : Int))
        (hlast : elem nums' (n : Int) = x), ∀ r r' : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          Aegis.MinimumOperations.minimum_operations nums' = ok r' → r.val = r'.val) := by
    sorry

  /-- Whenever the function returns r, r <= q = (n-1) div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and n = 3*q + 1 for some integer q >= 0. -/
  theorem spec_14 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
      (q : Nat) (hq : n = 3 * q + 1) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r → r.val ≤ (q : Int) := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
        (q : Nat) (hq : n = 3 * q + 1), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r → r.val ≤ (q : Int)) := by
    sorry

  /-- Whenever the function returns r, r = q+1 if and only if nums[n-2] = nums[n-1]. Here q = (n-2) div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and n = 3*q + 2 for some integer q >= 0. -/
  theorem spec_15 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
      (q : Nat) (hq : n = 3 * q + 2) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (r.val = (q : Int) + 1 ↔ elem nums ((n : Int) - 2) = elem nums ((n : Int) - 1)) := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
        (q : Nat) (hq : n = 3 * q + 2), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (r.val = (q : Int) + 1 ↔ elem nums ((n : Int) - 2) = elem nums ((n : Int) - 1))) := by
    sorry

  /-- Whenever the function returns r, r = q if and only if the last three elements nums[n-3], nums[n-2], nums[n-1] are not pairwise distinct, i.e. there exist i and j with n-3 <= i < j <= n-1 and nums[i] = nums[j]. Here q = n div 3.
    Preconditions: Let n = len(nums). Assume 1 <= n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and n = 3*q for some integer q >= 1. -/
  theorem spec_16 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
      (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
      (q : Nat) (hq : n = 3 * q) (hq_lo : 1 ≤ q) :
      ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
        (r.val = (q : Int) ↔
          ∃ i j : Int, (n : Int) - 3 ≤ i ∧ i < j ∧ j ≤ (n : Int) - 1 ∧ elem nums i = elem nums j) := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100)
        (hval : ∀ i : Nat, i < n → 1 ≤ elem nums (i : Int) ∧ elem nums (i : Int) ≤ 100)
        (q : Nat) (hq : n = 3 * q) (hq_lo : 1 ≤ q), ∀ r : Std.I64, Aegis.MinimumOperations.minimum_operations nums = ok r →
          (r.val = (q : Int) ↔
            ∃ i j : Int, (n : Int) - 3 ≤ i ∧ i < j ∧ j ≤ (n : Int) - 1 ∧ elem nums i = elem nums j)) := by
    sorry

  end AegisSpec.MinimumOperations
