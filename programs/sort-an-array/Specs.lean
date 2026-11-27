import Aegis.SortArray.Code.Funs

/-!
# Specifications of `Aegis.SortArray.sort_array`

LeetCode problem `sort-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SortArray

namespace AegisSpec.SortArray

def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

def countOcc (l : List Std.I64) (v : Int) : ℕ := (vals l).count v

def IsSorted (l : List Std.I64) : Prop :=
  ∀ i (h : i + 1 < l.length), (l[i]'(by omega)).val ≤ (l[i+1]'h).val

def IsMin (l : List Std.I64) (m : Int) : Prop :=
  (∃ (j : ℕ) (h : j < l.length), (l[j]'h).val = m) ∧ ∀ j (h : j < l.length), m ≤ (l[j]'h).val

def IsMax (l : List Std.I64) (M : Int) : Prop :=
  (∃ (j : ℕ) (h : j < l.length), (l[j]'h).val = M) ∧ ∀ j (h : j < l.length), (l[j]'h).val ≤ M

def firstVal (l : List Std.I64) (h : 0 < l.length) : Int := (l.get ⟨0, h⟩).val

def lastVal (l : List Std.I64) (h : 0 < l.length) : Int :=
  (l.get ⟨l.length - 1, Nat.sub_lt h Nat.one_pos⟩).val

/-- The function returns a result r (it does not fail). Let count(xs,v) be the number of indices i with 0 <= i < len(xs) and xs[i] = v. Then: (1) len(r) = len(nums); (2) for every i with 0 <= i < len(r)-1, r[i] <= r[i+1]; (3) for every integer v, count(r,v) = count(nums,v).
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_1 (nums : Slice Std.I64) (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000) :
    ∃ r : alloc.vec.Vec Std.I64, sort_array nums = ok r ∧ r.val.length = nums.val.length ∧
      IsSorted r.val ∧ ∀ v : Int, countOcc r.val v = countOcc nums.val v := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000), ∃ r : alloc.vec.Vec Std.I64, sort_array nums = ok r ∧ r.val.length = nums.val.length ∧
      IsSorted r.val ∧ ∀ v : Int, countOcc r.val v = countOcc nums.val v) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums).
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_2 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) : r.val.length = nums.val.length := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), r.val.length = nums.val.length) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r)-1, r[i] <= r[i+1].
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_3 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) : IsSorted r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), IsSorted r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, the number of indices i with 0 <= i < len(r) and r[i] = v equals the number of indices i with 0 <= i < len(nums) and nums[i] = v.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_4 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) :
    ∀ v : Int, countOcc r.val v = countOcc nums.val v := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), ∀ v : Int, countOcc r.val v = countOcc nums.val v) := by
  sorry

/-- Whenever the function returns a result r, there exists a bijection π from {0, ..., len(r)-1} to {0, ..., len(nums)-1} such that for every i with 0 <= i < len(r), r[i] = nums[π(i)].
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_5 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) :
    ∃ π : Fin r.val.length → Fin nums.val.length,
      Function.Bijective π ∧ ∀ i : Fin r.val.length, (r.val.get i).val = (nums.val.get (π i)).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), ∃ π : Fin r.val.length → Fin nums.val.length,
      Function.Bijective π ∧ ∀ i : Fin r.val.length, (r.val.get i).val = (nums.val.get (π i)).val) := by
  sorry

/-- Whenever the function returns a result r, let m be the minimum of nums, i.e. the integer m such that m = nums[j] for some j with 0 <= j < len(nums) and m <= nums[j] for every j with 0 <= j < len(nums). Then len(r) > 0 and r[0] = m.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_6 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) :
    r.val.length > 0 ∧
      ∀ (m : Int), IsMin nums.val m → ∀ (h0 : 0 < r.val.length), firstVal r.val h0 = m := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), r.val.length > 0 ∧
      ∀ (m : Int), IsMin nums.val m → ∀ (h0 : 0 < r.val.length), firstVal r.val h0 = m) := by
  sorry

/-- Whenever the function returns a result r, let M be the maximum of nums, i.e. the integer M such that M = nums[j] for some j with 0 <= j < len(nums) and M >= nums[j] for every j with 0 <= j < len(nums). Then len(r) > 0 and r[len(r)-1] = M.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_7 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) :
    r.val.length > 0 ∧
      ∀ (M : Int), IsMax nums.val M → ∀ (h0 : 0 < r.val.length), lastVal r.val h0 = M := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), r.val.length > 0 ∧
      ∀ (M : Int), IsMax nums.val M → ∀ (h0 : 0 < r.val.length), lastVal r.val h0 = M) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < len(r), min(nums) <= r[i] <= max(nums), where min(nums) and max(nums) are the minimum and maximum values occurring in nums.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_8 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) :
    ∀ (mn mx : Int), IsMin nums.val mn → IsMax nums.val mx →
      ∀ i (h : i < r.val.length), mn ≤ (r.val[i]'h).val ∧ (r.val[i]'h).val ≤ mx := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), ∀ (mn mx : Int), IsMin nums.val mn → IsMax nums.val mx →
      ∀ i (h : i < r.val.length), mn ≤ (r.val[i]'h).val ∧ (r.val[i]'h).val ≤ mx) := by
  sorry

/-- Whenever the function returns a result r, if nums is nondecreasing (for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]), then len(r) = len(nums) and for every i with 0 <= i < len(nums), r[i] = nums[i].
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_9 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) (hsorted : IsSorted nums.val) :
    r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < r.val.length) (hj : i < nums.val.length),
        (r.val[i]'hi).val = (nums.val[i]'hj).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) (hsorted : IsSorted nums.val), r.val.length = nums.val.length ∧
      ∀ (i : ℕ) (hi : i < r.val.length) (hj : i < nums.val.length),
        (r.val[i]'hi).val = (nums.val[i]'hj).val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r (it does not fail).
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_10 (nums : Slice Std.I64) (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000) :
    ∃ r : alloc.vec.Vec Std.I64, sort_array nums = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000), ∃ r : alloc.vec.Vec Std.I64, sort_array nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, the sum of all elements of r equals the sum of all elements of nums, where sums are taken as mathematical integers: sum_{i=0}^{len(r)-1} r[i] = sum_{i=0}^{len(nums)-1} nums[i].
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -50000 <= nums[i] <= 50000. -/
theorem spec_11 (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r) : (vals r.val).sum = (vals nums.val).sum := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : alloc.vec.Vec Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 50000)
    (hval : ∀ i (h : i < nums.val.length),
      -50000 ≤ (nums.val[i]'h).val ∧ (nums.val[i]'h).val ≤ 50000)
    (hr : sort_array nums = ok r), (vals r.val).sum = (vals nums.val).sum) := by
  sorry

end AegisSpec.SortArray
