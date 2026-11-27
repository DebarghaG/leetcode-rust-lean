import Aegis.DistinctDifferenceArray.Code.Funs

/-!
# Specifications of `Aegis.DistinctDifferenceArray.distinct_difference_array`

LeetCode problem `find-the-distinct-difference-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DistinctDifferenceArray

  open Aegis.DistinctDifferenceArray

  def numDistinctIn (l : List Std.I64) (a b : ℕ) : ℕ :=
    ((l.drop a).take (b - a)).dedup.length

  def prefixDistinct (nums : Slice Std.I64) (i : ℕ) : ℕ :=
    numDistinctIn nums.val 0 (i + 1)

  def suffixDistinct (nums : Slice Std.I64) (i : ℕ) : ℕ :=
    numDistinctIn nums.val (i + 1) nums.val.length

  def contents (r : alloc.vec.Vec Std.I64) : List ℤ :=
    r.val.map (fun x => x.val)

  /-- The function returns a result r (it does not fail) such that len(r) = n, and for every i with 0 <= i < n, r[i] = P_i - S_i, where P_i is the number of distinct values occurring in the prefix nums[0, ..., i], and S_i is the number of distinct values occurring in the suffix nums[i+1, ..., n-1]. The suffix count is 0 when i = n-1 (empty suffix). A value v counts in P_i exactly when there exists j with 0 <= j <= i and nums[j] = v; it counts in S_i exactly when there exists j with i+1 <= j <= n-1 and nums[j] = v.
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∃ r : alloc.vec.Vec Std.I64,
        distinct_difference_array nums = ok r ∧
        r.val.length = nums.val.length ∧
        ∀ (i : ℕ) (hi : i < r.val.length),
          (r.val[i]'hi).val
            = (prefixDistinct nums i : ℤ) - (suffixDistinct nums i : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∃ r : alloc.vec.Vec Std.I64,
          distinct_difference_array nums = ok r ∧
          r.val.length = nums.val.length ∧
          ∀ (i : ℕ) (hi : i < r.val.length),
            (r.val[i]'hi).val
              = (prefixDistinct nums i : ℤ) - (suffixDistinct nums i : ℤ)) := by
    sorry

  /-- The function returns a result r; it does not fail for any input satisfying the preconditions (no overflow, out-of-bounds access, or panic).
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∃ r : alloc.vec.Vec Std.I64, distinct_difference_array nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∃ r : alloc.vec.Vec Std.I64, distinct_difference_array nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, for every i with 0 <= i < n we have i + 2 - n <= r[i] <= i + 1.
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        ∀ (i : ℕ) (hi : i < nums.val.length),
          (i : ℤ) + 2 - (nums.val.length : ℤ) ≤ (r.val[i]'(by omega)).val ∧
          (r.val[i]'(by omega)).val ≤ (i : ℤ) + 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          ∀ (i : ℕ) (hi : i < nums.val.length),
            (i : ℤ) + 2 - (nums.val.length : ℤ) ≤ (r.val[i]'(by omega)).val ∧
            (r.val[i]'(by omega)).val ≤ (i : ℤ) + 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, r[0] = 1 - T, where T is the number of distinct values occurring in nums[1, ..., n-1], and T = 0 when n = 1 (empty suffix).
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        (r.val[0]'(by omega)).val
          = 1 - (numDistinctIn nums.val 1 nums.val.length : ℤ) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          (r.val[0]'(by omega)).val
            = 1 - (numDistinctIn nums.val 1 nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, r[n-1] = U, where U is the number of distinct values occurring in the whole array nums[0, ..., n-1].
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        (r.val[nums.val.length - 1]'(by omega)).val
          = (numDistinctIn nums.val 0 nums.val.length : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          (r.val[nums.val.length - 1]'(by omega)).val
            = (numDistinctIn nums.val 0 nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 1 and r[0] = 1.
    Preconditions: Let n = len(nums). n = 1 and 1 <= nums[0] <= 50. -/
  theorem spec_7 (nums : Slice Std.I64) (hn : nums.val.length = 1)
      (hval : 1 ≤ (nums.val[0]'(by omega)).val ∧
        (nums.val[0]'(by omega)).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        r.val.length = 1 ∧ contents r = [(1 : ℤ)] := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (hn : nums.val.length = 1)
        (hval : 1 ≤ (nums.val[0]'(by omega)).val ∧
          (nums.val[0]'(by omega)).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          r.val.length = 1 ∧ contents r = [(1 : ℤ)]) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, for every i with 0 <= i < n, r[i] = (i + 1) - (n - 1 - i) = 2*i + 2 - n.
    Preconditions: Let n = len(nums). 1 <= n <= 50, for every i with 0 <= i < n, 1 <= nums[i] <= 50, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
      (hnd : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        i < j → (nums.val[i]'hi) ≠ (nums.val[j]'hj)) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        ∀ (i : ℕ) (hi : i < nums.val.length),
          (r.val[i]'(by omega)).val
            = 2 * (i : ℤ) + 2 - (nums.val.length : ℤ) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
        (hnd : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
          i < j → (nums.val[i]'hi) ≠ (nums.val[j]'hj)), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          ∀ (i : ℕ) (hi : i < nums.val.length),
            (r.val[i]'(by omega)).val
              = 2 * (i : ℤ) + 2 - (nums.val.length : ℤ)) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, r is the length-n vector whose entries at indices 0 through n-2 are all 0 and whose entry at index n-1 is 1.
    Preconditions: Let n = len(nums). 1 <= n <= 50, for every i with 0 <= i < n, 1 <= nums[i] <= 50, and for every i, j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
      (hall : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
        (nums.val[i]'hi) = (nums.val[j]'hj)) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        (∀ (i : ℕ) (h : i < nums.val.length - 1),
          (r.val[i]'(by omega)).val = 0) ∧
        (r.val[nums.val.length - 1]'(by omega)).val = 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50)
        (hall : ∀ (i j : ℕ) (hi : i < nums.val.length) (hj : j < nums.val.length),
          (nums.val[i]'hi) = (nums.val[j]'hj)), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          (∀ (i : ℕ) (h : i < nums.val.length - 1),
            (r.val[i]'(by omega)).val = 0) ∧
          (r.val[nums.val.length - 1]'(by omega)).val = 1) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, for every i with 0 <= i < n - 1, r[i] <= r[i + 1].
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        ∀ (i : ℕ) (h : i < nums.val.length - 1),
          (r.val[i]'(by omega)).val ≤ (r.val[i + 1]'(by omega)).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          ∀ (i : ℕ) (h : i < nums.val.length - 1),
            (r.val[i]'(by omega)).val ≤ (r.val[i + 1]'(by omega)).val) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = n, for every i with 0 <= i < n - 1, r[i + 1] <= r[i] + 2.
    Preconditions: Let n = len(nums). 1 <= n <= 50, and for every i with 0 <= i < n, 1 <= nums[i] <= 50. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
      (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = nums.val.length) →
        ∀ (i : ℕ) (h : i < nums.val.length - 1),
          (r.val[i + 1]'(by omega)).val ≤ (r.val[i]'(by omega)).val + 2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn1 : 1 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
        (hval : ∀ (i : ℕ) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = nums.val.length) →
          ∀ (i : ℕ) (h : i < nums.val.length - 1),
            (r.val[i + 1]'(by omega)).val ≤ (r.val[i]'(by omega)).val + 2) := by
    sorry

  /-- Whenever the function returns a result r with len(r) = 2, r is the length-2 vector [0, d], where d = 1 if nums[0] = nums[1] and d = 2 otherwise.
    Preconditions: Let n = len(nums). n = 2, 1 <= nums[0] <= 50, and 1 <= nums[1] <= 50. -/
  theorem spec_12 (nums : Slice Std.I64) (hn : nums.val.length = 2)
      (hval0 : 1 ≤ (nums.val[0]'(by omega)).val ∧
        (nums.val[0]'(by omega)).val ≤ 50)
      (hval1 : 1 ≤ (nums.val[1]'(by omega)).val ∧
        (nums.val[1]'(by omega)).val ≤ 50) :
      ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
        (hlen : r.val.length = 2) →
        contents r = [0, (if (nums.val[0]'(by omega)) = (nums.val[1]'(by omega))
          then (1 : ℤ) else 2)] := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (hn : nums.val.length = 2)
        (hval0 : 1 ≤ (nums.val[0]'(by omega)).val ∧
          (nums.val[0]'(by omega)).val ≤ 50)
        (hval1 : 1 ≤ (nums.val[1]'(by omega)).val ∧
          (nums.val[1]'(by omega)).val ≤ 50), ∀ (r : alloc.vec.Vec Std.I64), distinct_difference_array nums = ok r →
          (hlen : r.val.length = 2) →
          contents r = [0, (if (nums.val[0]'(by omega)) = (nums.val[1]'(by omega))
            then (1 : ℤ) else 2)]) := by
    sorry

  end AegisSpec.DistinctDifferenceArray
