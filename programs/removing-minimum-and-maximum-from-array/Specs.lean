import Aegis.MinimumDeletions.Code.Funs

/-!
# Specifications of `Aegis.MinimumDeletions.minimum_deletions`

LeetCode problem `removing-minimum-and-maximum-from-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinimumDeletions

def IsMinIndex (l : List Std.I64) (i : Nat) : Prop :=
  ∃ h : i < l.length, ∀ j (hj : j < l.length), (l[i]'h).val ≤ (l[j]'hj).val

def IsMaxIndex (l : List Std.I64) (i : Nat) : Prop :=
  ∃ h : i < l.length, ∀ j (hj : j < l.length), (l[j]'hj).val ≤ (l[i]'h).val

def EntriesInRange (l : List Std.I64) : Prop :=
  ∀ i (hi : i < l.length), -100000 ≤ (l[i]'hi).val ∧ (l[i]'hi).val ≤ 100000

def PairwiseDistinct (l : List Std.I64) : Prop :=
  ∀ i (hi : i < l.length) (j) (hj : j < l.length), i < j → l[i]'hi ≠ l[j]'hj

/-- Let n = len(nums). Let imin be the unique index with 0 <= imin < n and nums[imin] <= nums[i] for every i with 0 <= i < n, and let imax be the unique index with 0 <= imax < n and nums[imax] >= nums[i] for every i with 0 <= i < n. Put l = min(imin, imax) and h = max(imin, imax). Whenever the function returns a result res, res = the minimum of the three integers h + 1, n - l, and l + 1 + n - h.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_1 (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    res.val = ((min (min (max imin imax + 1) (nums.val.length - min imin imax))
      (min imin imax + 1 + (nums.val.length - max imin imax)) : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), res.val = ((min (min (max imin imax + 1) (nums.val.length - min imin imax))
      (min imin imax + 1 + (nums.val.length - max imin imax)) : Nat) : Int)) := by
  sorry

/-- The function returns a result res on every input satisfying the preconditions; it does not fail.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val) :
    ∃ res : Std.I64, Aegis.MinimumDeletions.minimum_deletions nums = ok res := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val), ∃ res : Std.I64, Aegis.MinimumDeletions.minimum_deletions nums = ok res) := by
  sorry

/-- Whenever the function returns a result res, 1 <= res <= n.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    1 ≤ res.val ∧ res.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), 1 ≤ res.val ∧ res.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result res, res >= 2.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume n >= 2, n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    2 ≤ res.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), 2 ≤ res.val) := by
  sorry

/-- Let imin and imax be the unique indices of the minimum and maximum elements of nums, and put l = min(imin, imax) and h = max(imin, imax). Whenever the function returns a result res, res = 2 if and only if at least one of the following three conditions holds: (1) h <= 1; (2) l >= n - 2; (3) l = 0 and h = n - 1.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume n >= 2, n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_5 (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    res.val = 2 ↔ (max imin imax ≤ 1 ∨ min imin imax ≥ nums.val.length - 2 ∨
      (min imin imax = 0 ∧ max imin imax = nums.val.length - 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 2 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), res.val = 2 ↔ (max imin imax ≤ 1 ∨ min imin imax ≥ nums.val.length - 2 ∨
      (min imin imax = 0 ∧ max imin imax = nums.val.length - 1))) := by
  sorry

/-- Let imin and imax be the unique indices of the minimum and maximum elements of nums. Whenever the function returns a result res, there exist integers a and b with a >= 0, b >= 0, and a + b = res such that after deleting the first a elements and the last b elements of nums, neither index imin nor index imax remains; equivalently, for each x in {imin, imax}, x < a or x >= n - b.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_6 (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    ∃ a b : Int, 0 ≤ a ∧ 0 ≤ b ∧ a + b = res.val ∧
      ((imin : Int) < a ∨ (imin : Int) ≥ (nums.val.length : Int) - b) ∧
      ((imax : Int) < a ∨ (imax : Int) ≥ (nums.val.length : Int) - b) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), ∃ a b : Int, 0 ≤ a ∧ 0 ≤ b ∧ a + b = res.val ∧
      ((imin : Int) < a ∨ (imin : Int) ≥ (nums.val.length : Int) - b) ∧
      ((imax : Int) < a ∨ (imax : Int) ≥ (nums.val.length : Int) - b)) := by
  sorry

/-- Let imin and imax be the unique indices of the minimum and maximum elements of nums. Whenever the function returns a result res, for every pair of integers a and b with a >= 0, b >= 0, and a + b < res, after deleting the first a elements and the last b elements of nums, at least one of imin and imax remains; equivalently, either a <= imin <= n - 1 - b or a <= imax <= n - 1 - b.
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_7 (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    ∀ a b : Int, 0 ≤ a → 0 ≤ b → a + b < res.val →
      (((imin : Int) ≥ a ∧ (imin : Int) ≤ (nums.val.length : Int) - 1 - b) ∨
       ((imax : Int) ≥ a ∧ (imax : Int) ≤ (nums.val.length : Int) - 1 - b)) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), ∀ a b : Int, 0 ≤ a → 0 ≤ b → a + b < res.val →
      (((imin : Int) ≥ a ∧ (imin : Int) ≤ (nums.val.length : Int) - 1 - b) ∨
       ((imax : Int) ≥ a ∧ (imax : Int) ≤ (nums.val.length : Int) - 1 - b))) := by
  sorry

/-- Let imin and imax be the unique indices of the minimum and maximum elements of nums. Whenever the function returns a result res, for each x in {imin, imax}, res >= min(x + 1, n - x).
  Preconditions: nums is a slice of 64-bit signed integers. Let n = len(nums). We assume 1 <= n <= 100000, for every i with 0 <= i < n, -100000 <= nums[i] <= 100000, and for every i, j with 0 <= i < j < n, nums[i] != nums[j]. -/
theorem spec_8 (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res) :
    ((min (imin + 1) (nums.val.length - imin) : Nat) : Int) ≤ res.val ∧
      ((min (imax + 1) (nums.val.length - imax) : Nat) : Int) ≤ res.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (imin imax : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (res : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res), ((min (imin + 1) (nums.val.length - imin) : Nat) : Int) ≤ res.val ∧
      ((min (imax + 1) (nums.val.length - imax) : Nat) : Int) ≤ res.val) := by
  sorry

/-- Whenever minimum_deletions(nums) returns a result res and minimum_deletions(rev) returns a result res', we have res = res'.
  Preconditions: nums is a slice of 64-bit signed integers satisfying 1 <= len(nums) <= 100000, all entries in [-100000,100000], and pairwise distinctness. Let n = len(nums). Let rev be any slice of length n such that rev[i] = nums[n - 1 - i] for every i with 0 <= i < n. -/
theorem spec_9 (nums rev : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hrevlen : rev.val.length = nums.val.length)
    (hrev : ∀ i, i < nums.val.length →
      (rev.val[i]?).map (fun x => x.val) = (nums.val[nums.val.length - 1 - i]?).map
        (fun x => x.val))
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions rev = ok res') :
    res.val = res'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hrevlen : rev.val.length = nums.val.length)
    (hrev : ∀ i, i < nums.val.length →
      (rev.val[i]?).map (fun x => x.val) = (nums.val[nums.val.length - 1 - i]?).map
        (fun x => x.val))
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions rev = ok res'), res.val = res'.val) := by
  sorry

/-- Let imin and imax be the unique indices of the minimum and maximum elements of nums, and let imin' and imax' be the unique indices of the minimum and maximum elements of nums'. If imin = imin' and imax = imax', then whenever minimum_deletions(nums) returns a result res and minimum_deletions(nums') returns a result res', we have res = res'.
  Preconditions: nums and nums' are two slices of 64-bit signed integers, both satisfying the input constraints: same length n with 1 <= n <= 100000, all entries in [-100000,100000], and pairwise distinct elements in each slice. -/
theorem spec_10 (nums nums' : Slice Std.I64) (imin imax imin' imax' : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hrange' : EntriesInRange nums'.val) (hdistinct' : PairwiseDistinct nums'.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (himin' : IsMinIndex nums'.val imin') (himax' : IsMaxIndex nums'.val imax')
    (heqmin : imin = imin') (heqmax : imax = imax')
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions nums' = ok res') :
    res.val = res'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (imin imax imin' imax' : Nat)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hrange' : EntriesInRange nums'.val) (hdistinct' : PairwiseDistinct nums'.val)
    (himin : IsMinIndex nums.val imin) (himax : IsMaxIndex nums.val imax)
    (himin' : IsMinIndex nums'.val imin') (himax' : IsMaxIndex nums'.val imax')
    (heqmin : imin = imin') (heqmax : imax = imax')
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions nums' = ok res'), res.val = res'.val) := by
  sorry

/-- Whenever minimum_deletions(nums) returns a result res and minimum_deletions(nums') returns a result res', we have res = res'.
  Preconditions: nums is a slice of 64-bit signed integers satisfying 1 <= len(nums) <= 100000, all entries in [-100000,100000], and pairwise distinctness. Let n = len(nums). Let c be an integer and nums' a slice of length n such that nums'[i] = nums[i] + c for every i with 0 <= i < n, and nums' also satisfies the input constraints (all entries in [-100000,100000] and pairwise distinct). -/
theorem spec_11 (nums nums' : Slice Std.I64) (c : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i (hi : i < nums.val.length),
      (nums'.val[i]'(by omega)).val = (nums.val[i]'hi).val + c)
    (hrange' : EntriesInRange nums'.val) (hdistinct' : PairwiseDistinct nums'.val)
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions nums' = ok res') :
    res.val = res'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : Int)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hrange : EntriesInRange nums.val) (hdistinct : PairwiseDistinct nums.val)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i (hi : i < nums.val.length),
      (nums'.val[i]'(by omega)).val = (nums.val[i]'hi).val + c)
    (hrange' : EntriesInRange nums'.val) (hdistinct' : PairwiseDistinct nums'.val)
    (res res' : Std.I64)
    (hres : Aegis.MinimumDeletions.minimum_deletions nums = ok res)
    (hres' : Aegis.MinimumDeletions.minimum_deletions nums' = ok res'), res.val = res'.val) := by
  sorry

end AegisSpec.MinimumDeletions
