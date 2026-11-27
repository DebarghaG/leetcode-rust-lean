import Aegis.IncremovableSubarrayCount.Code.Funs

/-!
# Specifications of `Aegis.IncremovableSubarrayCount.incremovable_subarray_count`

LeetCode problem `count-the-number-of-incremovable-subarrays-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IncremovableSubarrayCount

open Aegis.IncremovableSubarrayCount

open Classical

def StrictlyIncreasing : List I64 → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => a.val < b.val ∧ StrictlyIncreasing (b :: l)

def AllEqual (l : List I64) : Prop := ∀ a ∈ l, ∀ b ∈ l, a.val = b.val

def deleteBlock (nums : Slice I64) (l r : Nat) : List I64 :=
  nums.val.take l ++ nums.val.drop (r + 1)

def IncAfterDeletion (nums : Slice I64) (l r : Nat) : Prop :=
  StrictlyIncreasing (deleteBlock nums l r)

def Admissible (nums : Slice I64) (l r : Nat) : Prop :=
  l ≤ r ∧ r < nums.val.length ∧ IncAfterDeletion nums l r

noncomputable def admissiblePairs (nums : Slice I64) : Finset (Nat × Nat) :=
  (Finset.range nums.val.length ×ˢ Finset.range nums.val.length).filter
    (fun p => Admissible nums p.1 p.2)

noncomputable def admissibleCount (nums : Slice I64) : Nat :=
  (admissiblePairs nums).card

/-- Let n = len(nums). Call an index pair (l, r) admissible when 0 <= l <= r < n and the sequence obtained by deleting nums[l], nums[l+1], ..., nums[r] from nums, namely nums[0], nums[1], ..., nums[l-1], nums[r+1], nums[r+2], ..., nums[n-1] (all these entries kept in their original order), is strictly increasing: for every two consecutive entries a, b of this remaining sequence we have a < b. By definition the empty sequence and any one-element sequence are strictly increasing. The call returns a result res (an i64) such that res equals the number of admissible pairs (l, r).
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50) :
    ∃ res : I64,
      incremovable_subarray_count nums = ok res ∧
        res.val = (admissibleCount nums : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50), ∃ res : I64,
      incremovable_subarray_count nums = ok res ∧
        res.val = (admissibleCount nums : Int)) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. Then res <= n*(n+1)/2.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res) :
    res.val ≤ ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res), res.val ≤ ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. If n >= 2, then res >= 3. In particular the three distinct subarrays nums[0..n-1], nums[0..n-2] and nums[1..n-1] are all incremovable: removing nums[0..n-1] leaves the empty array, removing nums[0..n-2] leaves the single entry nums[n-1], and removing nums[1..n-1] leaves the single entry nums[0]; the empty array and any one-element array are strictly increasing.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 2 ≤ nums.val.length) :
    3 ≤ res.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 2 ≤ nums.val.length), 3 ≤ res.val) := by
  sorry

/-- If len(nums) = 1, the call returns res = 1.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hn : nums.val.length = 1) :
    ∃ res : I64, incremovable_subarray_count nums = ok res ∧ res.val = 1 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hn : nums.val.length = 1), ∃ res : I64, incremovable_subarray_count nums = ok res ∧ res.val = 1) := by
  sorry

/-- If len(nums) = 2, the call returns res = 3.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hn : nums.val.length = 2) :
    ∃ res : I64, incremovable_subarray_count nums = ok res ∧ res.val = 3 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hn : nums.val.length = 2), ∃ res : I64, incremovable_subarray_count nums = ok res ∧ res.val = 3) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. If nums is strictly increasing (for every i with 0 <= i < n-1, nums[i] < nums[i+1]), then res = n*(n+1)/2.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hinc : ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i]).val < (nums.val[i + 1]).val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res) :
    res.val = ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hinc : ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i]).val < (nums.val[i + 1]).val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res), res.val = ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result (it does not fail, panic, overflow, or go out of bounds).
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50) :
    ∃ res : I64, incremovable_subarray_count nums = ok res := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50), ∃ res : I64, incremovable_subarray_count nums = ok res) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. If n >= 3 and nums is strictly decreasing (for every i with 0 <= i < n-1, nums[i] > nums[i+1]), then res = 3.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_8 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hdec : ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i + 1]).val < (nums.val[i]).val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 3 ≤ nums.val.length) :
    res.val = 3 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (hdec : ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i + 1]).val < (nums.val[i]).val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 3 ≤ nums.val.length), res.val = 3) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. If n >= 2 and all entries of nums are equal (nums[i] = nums[j] for all 0 <= i, j < n), then res = 3.
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_9 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (heq : AllEqual nums.val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 2 ≤ nums.val.length) :
    res.val = 3 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (heq : AllEqual nums.val)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 2 ≤ nums.val.length), res.val = 3) := by
  sorry

/-- Suppose that for every pair of indices i, j with 0 <= i, j < n, a[i] < a[j] if and only if b[i] < b[j]. Then incremovable_subarray_count(a) = incremovable_subarray_count(b).
  Preconditions: 1 <= len(a) = len(b) = n <= 50, and 1 <= a[i], b[i] <= 50 for every 0 <= i < n. -/
theorem spec_10 (a b : Slice I64)
    (hlen_lower : 1 ≤ a.val.length) (hlen_eq : a.val.length = b.val.length)
    (hlen_upper : a.val.length ≤ 50)
    (hval_a : ∀ (i : Nat) (hi : i < a.val.length),
      1 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 50)
    (hval_b : ∀ (i : Nat) (hi : i < b.val.length),
      1 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 50)
    (hcmp : ∀ (i j : Nat) (hi : i < a.val.length) (hj : j < a.val.length),
      ((a.val[i]).val < (a.val[j]).val ↔ (b.val[i]).val < (b.val[j]).val)) :
    incremovable_subarray_count a = incremovable_subarray_count b := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (a b : Slice I64)
    (hlen_lower : 1 ≤ a.val.length) (hlen_eq : a.val.length = b.val.length)
    (hlen_upper : a.val.length ≤ 50)
    (hval_a : ∀ (i : Nat) (hi : i < a.val.length),
      1 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 50)
    (hval_b : ∀ (i : Nat) (hi : i < b.val.length),
      1 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 50)
    (hcmp : ∀ (i j : Nat) (hi : i < a.val.length) (hj : j < a.val.length),
      ((a.val[i]).val < (a.val[j]).val ↔ (b.val[i]).val < (b.val[j]).val)), incremovable_subarray_count a = incremovable_subarray_count b) := by
  sorry

/-- Let n = len(nums) and let res be the returned value. If n >= 3 and res = n*(n+1)/2, then nums is strictly increasing (for every i with 0 <= i < n-1, nums[i] < nums[i+1]).
  Preconditions: 1 <= len(nums) <= 50 and 1 <= nums[i] <= 50 for every 0 <= i < len(nums). -/
theorem spec_11 (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 3 ≤ nums.val.length)
    (hfull : res.val = ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2) :
    ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i]).val < (nums.val[i + 1]).val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64)
    (hlen_lower : 1 ≤ nums.val.length) (hlen_upper : nums.val.length ≤ 50)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 50)
    (res : I64) (hres : incremovable_subarray_count nums = ok res)
    (hn : 3 ≤ nums.val.length)
    (hfull : res.val = ((nums.val.length : Int) * ((nums.val.length : Int) + 1)) / 2), ∀ (i : Nat) (hi : i < nums.val.length - 1),
      (nums.val[i]).val < (nums.val[i + 1]).val) := by
  sorry

end AegisSpec.IncremovableSubarrayCount
