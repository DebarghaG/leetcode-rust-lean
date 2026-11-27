import Aegis.MaxAscendingSum.Code.Funs

/-!
# Specifications of `Aegis.MaxAscendingSum.max_ascending_sum`

LeetCode problem `maximum-ascending-subarray-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxAscendingSum

def vals (nums : Slice Std.I64) : List Int := nums.val.map fun x => x.val

def listMax : List Int → Int
  | [] => 0
  | x :: xs => xs.foldr max x

def segSum (nums : Slice Std.I64) (i j : Nat) : Int :=
  ((vals nums).drop i).take (j + 1 - i) |>.sum

def IncRun (nums : Slice Std.I64) (i j : Nat) : Prop :=
  ∀ (k : Nat) (h1 : i ≤ k) (h2 : k < j) (h3 : k + 1 < nums.val.length),
    (nums.val[k]'(by omega)).val < (nums.val[k + 1]'(by omega)).val

def incRunBool (nums : Slice Std.I64) (i j : Nat) : Bool :=
  (((vals nums).drop i).take (j + 1 - i)).zip
      (((vals nums).drop (i + 1)).take (j - i)) |>.all
    fun p => decide (p.1 < p.2)

def windowSums (nums : Slice Std.I64) (a b : Nat) : List Int :=
  (((List.range (b + 1)).flatMap fun i => (List.range (b + 1)).map fun j => (i, j))).filterMap
    fun p =>
      if a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b ∧ incRunBool nums p.1 p.2 = true
      then some (segSum nums p.1 p.2) else none

def Best (nums : Slice Std.I64) (a b : Nat) : Int := listMax (windowSums nums a b)

def maxElem (nums : Slice Std.I64) : Int := listMax (vals nums)

def StartsRun (nums : Slice Std.I64) (l : Nat) : Prop :=
  l = 0 ∨ ∃ (hl : 0 < l) (hl' : l < nums.val.length),
    (nums.val[l - 1]'(by omega)).val ≥ (nums.val[l]'hl').val

def EndsRun (nums : Slice Std.I64) (t : Nat) : Prop :=
  t + 1 = nums.val.length ∨ ∃ (ht : t + 1 < nums.val.length),
    (nums.val[t]'(by omega)).val ≥ (nums.val[t + 1]'ht).val

/-- The function returns a result r and r equals the maximum of the set of all sums sum_{k=i}^{j} nums[k] such that 0 <= i <= j < n and, for every k with i <= k < j, nums[k] < nums[k+1]. The set is nonempty because every singleton i = j is allowed, so the maximum is well defined; in particular the function does not fail.
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100) :
    ∃ r : Std.I64, Aegis.MaxAscendingSum.max_ascending_sum nums = ok r ∧
      (∀ (i j : Nat), i ≤ j → j < nums.val.length → IncRun nums i j →
        segSum nums i j ≤ r.val) ∧
      (∃ (i j : Nat), i ≤ j ∧ j < nums.val.length ∧ IncRun nums i j ∧
        segSum nums i j = r.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100), ∃ r : Std.I64, Aegis.MaxAscendingSum.max_ascending_sum nums = ok r ∧
      (∀ (i j : Nat), i ≤ j → j < nums.val.length → IncRun nums i j →
        segSum nums i j ≤ r.val) ∧
      (∃ (i j : Nat), i ≤ j ∧ j < nums.val.length ∧ IncRun nums i j ∧
        segSum nums i j = r.val)) := by
  sorry

/-- For every nums satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100) :
    ∃ r : Std.I64, Aegis.MaxAscendingSum.max_ascending_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100), ∃ r : Std.I64, Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{k=0}^{n-1} nums[k].
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    r.val ≤ segSum nums 0 (nums.val.length - 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), r.val ≤ segSum nums 0 (nums.val.length - 1)) := by
  sorry

/-- Whenever the function returns a result r, for every i and j with 0 <= i <= j < n and for every k with i <= k < j, nums[k] < nums[k+1], we have sum_{k=i}^{j} nums[k] <= r.
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    ∀ (i j : Nat), i ≤ j → j < nums.val.length → IncRun nums i j →
      segSum nums i j ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), ∀ (i j : Nat), i ≤ j → j < nums.val.length → IncRun nums i j →
      segSum nums i j ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exist i and j with 0 <= i <= j < n such that, for every k with i <= k < j, nums[k] < nums[k+1], and sum_{k=i}^{j} nums[k] = r.
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    ∃ (i j : Nat), i ≤ j ∧ j < nums.val.length ∧ IncRun nums i j ∧
      segSum nums i j = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), ∃ (i j : Nat), i ≤ j ∧ j < nums.val.length ∧ IncRun nums i j ∧
      segSum nums i j = r.val) := by
  sorry

/-- Whenever the function returns a result r, r = nums[0].
  Preconditions: Let n = len(nums). n = 1 and 1 <= nums[0] <= 100. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn : nums.val.length = 1)
    (hbound : 1 ≤ (nums.val[0]'(by omega)).val ∧
      (nums.val[0]'(by omega)).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    r.val = (nums.val[0]'(by omega)).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : nums.val.length = 1)
    (hbound : 1 ≤ (nums.val[0]'(by omega)).val ∧
      (nums.val[0]'(by omega)).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), r.val = (nums.val[0]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r, r = sum_{k=0}^{n-1} nums[k].
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and for every i with 0 <= i < n-1, nums[i] < nums[i+1]. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (hinc : ∀ (i : Nat) (hi : i + 1 < nums.val.length),
      (nums.val[i]'(by omega)).val < (nums.val[i + 1]'hi).val)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    r.val = segSum nums 0 (nums.val.length - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (hinc : ∀ (i : Nat) (hi : i + 1 < nums.val.length),
      (nums.val[i]'(by omega)).val < (nums.val[i + 1]'hi).val)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), r.val = segSum nums 0 (nums.val.length - 1)) := by
  sorry

/-- Whenever the function returns a result r, r = max_{0 <= i < n} nums[i].
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, for every i with 0 <= i < n, 1 <= nums[i] <= 100, and for every i with 0 <= i < n-1, nums[i] >= nums[i+1]. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (hdec : ∀ (i : Nat) (hi : i + 1 < nums.val.length),
      (nums.val[i]'(by omega)).val ≥ (nums.val[i + 1]'hi).val)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    r.val = maxElem nums := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (hdec : ∀ (i : Nat) (hi : i + 1 < nums.val.length),
      (nums.val[i]'(by omega)).val ≥ (nums.val[i + 1]'hi).val)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), r.val = maxElem nums) := by
  sorry

/-- Whenever the function returns a result r, r equals the maximum of the set of sums sum_{k=l}^{t} nums[k] over all intervals [l,t] with 0 <= l <= t < n that satisfy all three conditions: (i) for every k with l <= k < t, nums[k] < nums[k+1]; (ii) l = 0 or nums[l-1] >= nums[l]; (iii) t = n-1 or nums[t] >= nums[t+1]. These intervals are exactly the maximal strictly increasing contiguous runs.
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    (∀ (l t : Nat), l ≤ t → t < nums.val.length → IncRun nums l t →
      StartsRun nums l → EndsRun nums t → segSum nums l t ≤ r.val) ∧
    (∃ (l t : Nat), l ≤ t ∧ t < nums.val.length ∧ IncRun nums l t ∧
      StartsRun nums l ∧ EndsRun nums t ∧ segSum nums l t = r.val) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), (∀ (l t : Nat), l ≤ t → t < nums.val.length → IncRun nums l t →
      StartsRun nums l → EndsRun nums t → segSum nums l t ≤ r.val) ∧
    (∃ (l t : Nat), l ≤ t ∧ t < nums.val.length ∧ IncRun nums l t ∧
      StartsRun nums l ∧ EndsRun nums t ∧ segSum nums l t = r.val)) := by
  sorry

/-- Whenever the function returns a result r, r = if nums[0] < nums[1] then nums[0] + nums[1] else max(nums[0], nums[1]).
  Preconditions: Let n = len(nums). n = 2, 1 <= nums[0] <= 100, and 1 <= nums[1] <= 100. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn : nums.val.length = 2)
    (h0lo : 1 ≤ (nums.val[0]'(by omega)).val)
    (h0hi : (nums.val[0]'(by omega)).val ≤ 100)
    (h1lo : 1 ≤ (nums.val[1]'(by omega)).val)
    (h1hi : (nums.val[1]'(by omega)).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r) :
    r.val = if (nums.val[0]'(by omega)).val < (nums.val[1]'(by omega)).val
            then (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val
            else max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn : nums.val.length = 2)
    (h0lo : 1 ≤ (nums.val[0]'(by omega)).val)
    (h0hi : (nums.val[0]'(by omega)).val ≤ 100)
    (h1lo : 1 ≤ (nums.val[1]'(by omega)).val)
    (h1hi : (nums.val[1]'(by omega)).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r), r.val = if (nums.val[0]'(by omega)).val < (nums.val[1]'(by omega)).val
            then (nums.val[0]'(by omega)).val + (nums.val[1]'(by omega)).val
            else max (nums.val[0]'(by omega)).val (nums.val[1]'(by omega)).val) := by
  sorry

/-- Whenever the function returns a result r, for every p with 0 <= p < n-1 and nums[p] >= nums[p+1], the following holds: r = max(Best(0,p), Best(p+1,n-1)), where for any 0 <= a <= b < n, Best(a,b) is defined as the maximum of the set of sums sum_{k=i}^{j} nums[k] such that a <= i <= j <= b and, for every k with i <= k < j, nums[k] < nums[k+1].
  Preconditions: Let n = len(nums). n >= 1 and n <= 100, and for every i with 0 <= i < n, 1 <= nums[i] <= 100. -/
theorem spec_11 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r)
    (p : Nat) (hp : p + 1 < nums.val.length)
    (hdesc : (nums.val[p]'(by omega)).val ≥ (nums.val[p + 1]'hp).val) :
    r.val = max (Best nums 0 p) (Best nums (p + 1) (nums.val.length - 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100)
    (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxAscendingSum.max_ascending_sum nums = ok r)
    (p : Nat) (hp : p + 1 < nums.val.length)
    (hdesc : (nums.val[p]'(by omega)).val ≥ (nums.val[p + 1]'hp).val), r.val = max (Best nums 0 p) (Best nums (p + 1) (nums.val.length - 1))) := by
  sorry

end AegisSpec.MaxAscendingSum
