import Aegis.LongestEqualSubarray.Code.Funs

/-!
# Specifications of `Aegis.LongestEqualSubarray.longest_equal_subarray`

LeetCode problem `find-the-longest-equal-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.LongestEqualSubarray

namespace AegisSpec.LongestEqualSubarray

def vals (l : List Std.I64) : List Int := l.map (fun x => x.val)

def freq (l : List Std.I64) (v : Int) : Nat :=
  (vals l).countP (fun x => x = v)

def valuesOf (l : List Std.I64) : Finset Int := (vals l).toFinset

def cnt (l : List Std.I64) (v : Int) (a b : Nat) : Nat :=
  ((l.drop a).take (b + 1 - a)).countP (fun x => x.val = v)

def rangeConst (l : List Std.I64) (a b : Nat) : Prop :=
  ∀ x ∈ (l.drop a).take (b + 1 - a),
    ∀ y ∈ (l.drop a).take (b + 1 - a), x.val = y.val

def allEq (l : List Std.I64) : Prop :=
  ∀ x ∈ vals l, ∀ y ∈ vals l, x = y

def allDistinct (l : List Std.I64) : Prop := (vals l).Nodup

noncomputable def maxCnt (l : List Std.I64) (k : Int) : Nat := by
  classical
  exact
    ((((Finset.range l.length).product (Finset.range l.length)).product
        (valuesOf l)).filter
        (fun q => q.1.1 ≤ q.1.2 ∧
          ((q.1.2 : Int) - (q.1.1 : Int) + 1 - (cnt l q.2 q.1.1 q.1.2 : Int) ≤ k))).sup
      (fun q => cnt l q.2 q.1.1 q.1.2)

noncomputable def maxSameValueLen (l : List Std.I64) : Nat := by
  classical
  exact
    (((Finset.range l.length).product (Finset.range l.length)).filter
        (fun p => p.1 ≤ p.2 ∧ rangeConst l p.1 p.2)).sup
      (fun p => p.2 + 1 - p.1)

noncomputable def maxFreq (l : List Std.I64) : Nat :=
  (valuesOf l).sup (freq l)

def rev (l : List Std.I64) : List Std.I64 := l.reverse

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int)) :
    ∃ r : Std.I64, longest_equal_subarray nums k = ok r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int)), ∃ r : Std.I64, longest_equal_subarray nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = max { cnt(v,a,b) | v is an integer, 0 <= a <= b < len(nums), and (b-a+1) - cnt(v,a,b) <= k }, where cnt(v,a,b) is the number of indices i with a <= i <= b and nums[i] = v.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    r.val = (maxCnt nums.val k.val : Int) := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), r.val = (maxCnt nums.val k.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, r <= len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist an integer v and indices a,b with 0 <= a <= b < len(nums) such that, writing c = #{i | a <= i <= b and nums[i] = v}, we have r = c and (b-a+1) - c <= k.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    ∃ (v : Int) (a b : Nat), a ≤ b ∧ b < nums.val.length ∧
      r.val = (cnt nums.val v a b : Int) ∧
      ((b : Int) - (a : Int) + 1 - (cnt nums.val v a b : Int)) ≤ k.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), ∃ (v : Int) (a b : Nat), a ≤ b ∧ b < nums.val.length ∧
      r.val = (cnt nums.val v a b : Int) ∧
      ((b : Int) - (a : Int) + 1 - (cnt nums.val v a b : Int)) ≤ k.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer v and all indices a,b with 0 <= a <= b < len(nums), if (b-a+1) - #{i | a <= i <= b and nums[i] = v} <= k, then #{i | a <= i <= b and nums[i] = v} <= r.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    ∀ (v : Int) (a b : Nat), a ≤ b → b < nums.val.length →
      ((b : Int) - (a : Int) + 1 - (cnt nums.val v a b : Int)) ≤ k.val →
      (cnt nums.val v a b : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), ∀ (v : Int) (a b : Nat), a ≤ b → b < nums.val.length →
      ((b : Int) - (a : Int) + 1 - (cnt nums.val v a b : Int)) ≤ k.val →
      (cnt nums.val v a b : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, if k = 0, then r = max { b-a+1 | 0 <= a <= b < len(nums) and nums[i] = nums[a] for every i with a <= i <= b }.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hk : k.val = 0) :
    r.val = (maxSameValueLen nums.val : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hk : k.val = 0), r.val = (maxSameValueLen nums.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] = nums[j] for all 0 <= i < j < len(nums), then r = len(nums).
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hall : allEq nums.val) :
    r.val = (nums.val.length : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hall : allEq nums.val), r.val = (nums.val.length : Int)) := by
  sorry

/-- Whenever the function returns a result r, if k >= len(nums) - 1, then r = max { #{i | 0 <= i < len(nums) and nums[i] = v} | v is an integer }.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hk : (nums.val.length : Int) - 1 ≤ k.val) :
    r.val = (maxFreq nums.val : Int) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hk : (nums.val.length : Int) - 1 ≤ k.val), r.val = (maxFreq nums.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, if nums[i] != nums[j] for all 0 <= i < j < len(nums), then r = 1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hdistinct : allDistinct nums.val) :
    r.val = 1 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r)
    (hdistinct : allDistinct nums.val), r.val = 1) := by
  sorry

/-- Whenever the function returns a result r, for every a,b with 0 <= a <= b < len(nums) such that nums[i] = nums[a] for every i with a <= i <= b, we have r >= b-a+1.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    ∀ (a b : Nat), a ≤ b → b < nums.val.length → rangeConst nums.val a b →
      (b : Int) - (a : Int) + 1 ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), ∀ (a b : Nat), a ≤ b → b < nums.val.length → rangeConst nums.val a b →
      (b : Int) - (a : Int) + 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= max { #{i | 0 <= i < len(nums) and nums[i] = v} | v is an integer }.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    r.val ≤ (maxFreq nums.val : Int) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), r.val ≤ (maxFreq nums.val : Int)) := by
  sorry

/-- Whenever the function returns a result r, for every integer v, if len(nums) - #{i | 0 <= i < len(nums) and nums[i] = v} <= k, then r >= #{i | 0 <= i < len(nums) and nums[i] = v}.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_13 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    ∀ (v : Int), (nums.val.length : Int) - (freq nums.val v : Int) ≤ k.val →
      (freq nums.val v : Int) ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), ∀ (v : Int), (nums.val.length : Int) - (freq nums.val v : Int) ≤ k.val →
      (freq nums.val v : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k' with k <= k' <= len(nums), r <= max { cnt(v,a,b) | v is an integer, 0 <= a <= b < len(nums), and (b-a+1) - cnt(v,a,b) <= k' }, where cnt(v,a,b) is the number of indices i with a <= i <= b and nums[i] = v.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_14 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    ∀ (k' : Int), k.val ≤ k' → k' ≤ (nums.val.length : Int) →
      r.val ≤ (maxCnt nums.val k' : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), ∀ (k' : Int), k.val ≤ k' → k' ≤ (nums.val.length : Int) →
      r.val ≤ (maxCnt nums.val k' : Int)) := by
  sorry

/-- Whenever the function returns a result r, if rev is the array of length len(nums) with rev[i] = nums[len(nums)-1-i] for every 0 <= i < len(nums), then r = max { cnt_rev(v,a,b) | v is an integer, 0 <= a <= b < len(nums), and (b-a+1) - cnt_rev(v,a,b) <= k }, where cnt_rev(v,a,b) is the number of indices i with a <= i <= b and rev[i] = v.
  Preconditions: len(nums) >= 1, len(nums) <= 100000, 0 <= k <= len(nums), and for every i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums). -/
theorem spec_15 (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r) :
    r.val = (maxCnt (rev nums.val) k.val : Int) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hlen : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
    (hk_nonneg : 0 ≤ k.val) (hk_le : k.val ≤ (nums.val.length : Int))
    (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int))
    (r : Std.I64) (hr : longest_equal_subarray nums k = ok r), r.val = (maxCnt (rev nums.val) k.val : Int)) := by
  sorry

end AegisSpec.LongestEqualSubarray
