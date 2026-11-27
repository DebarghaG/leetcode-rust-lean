import Aegis.MaxAbsoluteSum.Code.Funs

/-!
# Specifications of `Aegis.MaxAbsoluteSum.max_absolute_sum`

LeetCode problem `maximum-absolute-sum-of-any-subarray`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxAbsoluteSum (max_absolute_sum)

namespace AegisSpec.MaxAbsoluteSum

def elems (nums : Slice Std.I64) : List Int := (nums.list.toList).map (fun x => x.val)

abbrev lenOf (nums : Slice Std.I64) : Nat := (elems nums).length

def elem (nums : Slice Std.I64) (i : Nat) (hi : i < lenOf nums) : Int := (elems nums)[i]'hi

theorem lenOf_eq_sliceLen (nums : Slice Std.I64) : lenOf nums = (Slice.len nums).val := by
  have h : (↑nums : List Std.I64) = nums.list.toList := rfl
  simp [lenOf, elems, Slice.len, h, Aeneas.Data.ListN.ListN_length]

def prefixSum (l : List Int) (k : Nat) : Int := (l.take k).sum

def segSum (l : List Int) (i j : Nat) : Int := prefixSum l (j + 1) - prefixSum l i

def nonemptySegSums (l : List Int) : Finset Int :=
  (((Finset.range l.length).product (Finset.range l.length)).filter (fun p => p.1 ≤ p.2)).image
    (fun p => segSum l p.1 p.2)

def segSums (l : List Int) : Finset Int := insert 0 (nonemptySegSums l)

def absSegSums (l : List Int) : Finset Int := insert 0 ((nonemptySegSums l).image (fun x => |x|))

def maxAbsSegSum (l : List Int) : Int := (absSegSums l).max' (by simp [absSegSums])

def maxSegSum (l : List Int) : Int := (segSums l).max' (by simp [segSums])

def minSegSum (l : List Int) : Int := (segSums l).min' (by simp [segSums])

def maxPrefixSum (l : List Int) : Int :=
  (Finset.range (l.length + 1)).sup' (by simp) (prefixSum l)

def minPrefixSum (l : List Int) : Int :=
  (Finset.range (l.length + 1)).inf' (by simp) (prefixSum l)

def posSum (l : List Int) : Int := (l.filter (fun x => 0 < x)).sum

def negSum (l : List Int) : Int := ((l.filter (fun x => x < 0)).map (fun x => -x)).sum

/-- The function returns a result r and r = max( {0} ∪ { abs(Sum_{i=l}^{u} nums[i]) | 0 <= l <= u < len(nums) } ), where abs(x) = x if x >= 0 and abs(x) = -x if x < 0, and Sum_{i=l}^{u} nums[i] = nums[l] + nums[l+1] + ... + nums[u]. In words, r is the maximum absolute sum among all contiguous subarrays of nums, including the empty subarray whose sum is 0.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = maxAbsSegSum (elems nums) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = maxAbsSegSum (elems nums)) := by
  sorry

/-- The function returns a result r and does not fail: no arithmetic overflow, no out-of-bounds access, and no panic occurs on this input.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= max(P, N), where P = Sum_{i: 0 <= i < len(nums) and nums[i] > 0} nums[i] (the sum of the positive elements) and N = Sum_{i: 0 <= i < len(nums) and nums[i] < 0} (-nums[i]) (the sum of the absolute values of the negative elements). In particular, r is non-negative.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ max (posSum (elems nums)) (negSum (elems nums)) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      0 ≤ r.val ∧ r.val ≤ max (posSum (elems nums)) (negSum (elems nums))) := by
  sorry

/-- The function returns a result r and, for every pair of indices l, u with 0 <= l <= u < len(nums), abs(Sum_{i=l}^{u} nums[i]) <= r, where abs(x) = x if x >= 0 and abs(x) = -x if x < 0 and Sum_{i=l}^{u} nums[i] = nums[l] + nums[l+1] + ... + nums[u]. Thus no nonempty contiguous subarray has absolute sum exceeding r.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      ∀ (l u : Nat), l ≤ u → u < lenOf nums → |segSum (elems nums) l u| ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      ∀ (l u : Nat), l ≤ u → u < lenOf nums → |segSum (elems nums) l u| ≤ r.val) := by
  sorry

/-- The function returns a result r for which there exists a (possibly empty) contiguous subarray with absolute sum exactly r: either r = 0 (witnessed by the empty subarray) or there exist indices l, u with 0 <= l <= u < len(nums) such that abs(Sum_{i=l}^{u} nums[i]) = r. Here abs(x) = x if x >= 0 and abs(x) = -x if x < 0 and Sum_{i=l}^{u} nums[i] = nums[l] + nums[l+1] + ... + nums[u].
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      (r.val = 0 ∨ ∃ (l u : Nat), l ≤ u ∧ u < lenOf nums ∧
        |segSum (elems nums) l u| = r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      (r.val = 0 ∨ ∃ (l u : Nat), l ≤ u ∧ u < lenOf nums ∧
        |segSum (elems nums) l u| = r.val)) := by
  sorry

/-- Let P[0] = 0 and, for each k with 1 <= k <= len(nums), P[k] = nums[0] + nums[1] + ... + nums[k-1]. Then the function returns a result r and r = (max_{0 <= k <= len(nums)} P[k]) - (min_{0 <= k <= len(nums)} P[k]).
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = maxPrefixSum (elems nums) - minPrefixSum (elems nums) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = maxPrefixSum (elems nums) - minPrefixSum (elems nums)) := by
  sorry

/-- Let M = max( {0} ∪ { Sum_{i=l}^{u} nums[i] | 0 <= l <= u < len(nums) } ) and let m = min( {0} ∪ { Sum_{i=l}^{u} nums[i] | 0 <= l <= u < len(nums) } ). Then the function returns a result r and r = max(M, -m). Here Sum_{i=l}^{u} nums[i] = nums[l] + nums[l+1] + ... + nums[u].
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = max (maxSegSum (elems nums)) (-(minSegSum (elems nums))) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = max (maxSegSum (elems nums)) (-(minSegSum (elems nums)))) := by
  sorry

/-- The function returns a result r and r = nums[0] + nums[1] + ... + nums[len(nums)-1], i.e. the absolute sum of the whole array.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. In addition, for every i with 0 <= i < len(nums), nums[i] >= 0. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hnneg : ∀ (i : Nat) (hi : i < lenOf nums), 0 ≤ elem nums i hi) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = (elems nums).sum := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hnneg : ∀ (i : Nat) (hi : i < lenOf nums), 0 ≤ elem nums i hi), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = (elems nums).sum) := by
  sorry

/-- The function returns a result r and r = -(nums[0] + nums[1] + ... + nums[len(nums)-1]), i.e. the absolute value of the sum of the whole array.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. In addition, for every i with 0 <= i < len(nums), nums[i] <= 0. -/
theorem spec_9 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hnpos : ∀ (i : Nat) (hi : i < lenOf nums), elem nums i hi ≤ 0) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = -((elems nums).sum) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hnpos : ∀ (i : Nat) (hi : i < lenOf nums), elem nums i hi ≤ 0), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = -((elems nums).sum)) := by
  sorry

/-- The function returns a result r and r = abs(nums[0]), where abs(x) = x if x >= 0 and abs(x) = -x if x < 0.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. In addition, len(nums) = 1. -/
theorem spec_10 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hone : lenOf nums = 1) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = |elem nums 0 (by omega)| := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (hone : lenOf nums = 1), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧ r.val = |elem nums 0 (by omega)|) := by
  sorry

/-- The function returns a result r and r = max(0, abs(nums[0]), abs(nums[1]), abs(nums[0] + nums[1])), where abs(x) = x if x >= 0 and abs(x) = -x if x < 0.
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. In addition, len(nums) = 2. -/
theorem spec_11 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (htwo : lenOf nums = 2) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = max (max (max 0 |elem nums 0 (by omega)|) |elem nums 1 (by omega)|)
        |elem nums 0 (by omega) + elem nums 1 (by omega)| := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000)
    (htwo : lenOf nums = 2), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      r.val = max (max (max 0 |elem nums 0 (by omega)|) |elem nums 1 (by omega)|)
        |elem nums 0 (by omega) + elem nums 1 (by omega)|) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if nums[i] = 0 for every integer i with 0 <= i < len(nums).
  Preconditions: The problem constraints hold: len(nums) is the number of elements of the slice nums, 1 <= len(nums) <= 100000, and for every integer i with 0 <= i < len(nums), -10000 <= nums[i] <= 10000. All elements are 64-bit signed integers. -/
theorem spec_12 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000) :
    ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < lenOf nums), elem nums i hi = 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ lenOf nums) (hlen_le : lenOf nums ≤ 100000)
    (hbnd : ∀ (i : Nat) (hi : i < lenOf nums),
      -10000 ≤ elem nums i hi ∧ elem nums i hi ≤ 10000), ∃ r : Std.I64, max_absolute_sum nums = ok r ∧
      (r.val = 0 ↔ ∀ (i : Nat) (hi : i < lenOf nums), elem nums i hi = 0)) := by
  sorry

end AegisSpec.MaxAbsoluteSum
