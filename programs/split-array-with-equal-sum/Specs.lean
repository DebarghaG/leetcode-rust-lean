import Aegis.SplitArray.Code.Funs

/-!
# Specifications of `Aegis.SplitArray.split_array`

LeetCode problem `split-array-with-equal-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SplitArray

def sub_sum (l : List Std.I64) (a b : Nat) : ℤ :=
  ((l.drop a).take (b + 1 - a)).map (fun x => x.val) |>.sum

def HasSplit (l : List Std.I64) : Prop :=
  ∃ i j k : Nat,
    0 < i ∧ i + 1 < j ∧ j + 1 < k ∧ k < l.length - 1 ∧
      sub_sum l 0 (i - 1) = sub_sum l (i + 1) (j - 1) ∧
      sub_sum l (i + 1) (j - 1) = sub_sum l (j + 1) (k - 1) ∧
      sub_sum l (j + 1) (k - 1) = sub_sum l (k + 1) (l.length - 1)

/-- Whenever split_array(nums) returns a Boolean result r, r is true if and only if there exist integers i, j, k such that 0 < i, i + 1 < j, j + 1 < k, k < n - 1, and sum(0, i - 1) = sum(i + 1, j - 1) = sum(j + 1, k - 1) = sum(k + 1, n - 1), where sum(l, r) denotes nums[l] + nums[l + 1] + ... + nums[r] for 0 <= l <= r < n. Equivalently, r is false exactly when no such triple (i, j, k) exists.
  Preconditions: Let n = len(nums). 1 <= n <= 2000. For every t with 0 <= t < n, -1000000 <= nums[t] <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000) :
    ∀ r : Bool,
      Aegis.SplitArray.split_array nums = ok r → (r = true ↔ HasSplit nums.val) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000), ∀ r : Bool,
      Aegis.SplitArray.split_array nums = ok r → (r = true ↔ HasSplit nums.val)) := by
  sorry

/-- The function split_array(nums) returns a result; it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). 1 <= n <= 2000. For every t with 0 <= t < n, -1000000 <= nums[t] <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000) :
    ∃ r : Bool, Aegis.SplitArray.split_array nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000), ∃ r : Bool, Aegis.SplitArray.split_array nums = ok r) := by
  sorry

/-- Whenever split_array(nums) returns r and split_array(rev) returns s, we have r = s.
  Preconditions: Let n = len(nums). 1 <= n <= 2000. For every t with 0 <= t < n, -1000000 <= nums[t] <= 1000000. Let rev be the slice of length n defined by rev[t] = nums[n - 1 - t] for every 0 <= t < n. -/
theorem spec_3 (nums rev : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000)
    (hrev_len : rev.val.length = nums.val.length)
    (hrev : ∀ t (ht : t < nums.val.length),
      (rev.val[t]'(by omega)).val = (nums.val[nums.val.length - 1 - t]'(by omega)).val) :
    ∀ r s : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        Aegis.SplitArray.split_array rev = ok s → r = s := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000)
    (hrev_len : rev.val.length = nums.val.length)
    (hrev : ∀ t (ht : t < nums.val.length),
      (rev.val[t]'(by omega)).val = (nums.val[nums.val.length - 1 - t]'(by omega)).val), ∀ r s : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        Aegis.SplitArray.split_array rev = ok s → r = s) := by
  sorry

/-- Whenever split_array(nums) returns r and split_array(v) returns s, we have r = s.
  Preconditions: Let n = len(nums). 1 <= n <= 2000. For every t with 0 <= t < n, -1000000 <= nums[t] <= 1000000. Let c be a nonzero integer, and let v be a slice of length n such that v[t] = c * nums[t] for every 0 <= t < n and -1000000 <= v[t] <= 1000000 for every 0 <= t < n. -/
theorem spec_4 (nums v : Slice Std.I64) (c : ℤ)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000)
    (hc : c ≠ 0)
    (hv_len : v.val.length = nums.val.length)
    (hscale : ∀ t (ht : t < nums.val.length),
      (v.val[t]'(by omega)).val = c * (nums.val[t]'ht).val)
    (hbounds_v : ∀ t (ht : t < v.val.length),
      -1000000 ≤ (v.val[t]'ht).val ∧ (v.val[t]'ht).val ≤ 1000000) :
    ∀ r s : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        Aegis.SplitArray.split_array v = ok s → r = s := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums v : Slice Std.I64) (c : ℤ)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hbounds : ∀ t (ht : t < nums.val.length),
      -1000000 ≤ (nums.val[t]'ht).val ∧ (nums.val[t]'ht).val ≤ 1000000)
    (hc : c ≠ 0)
    (hv_len : v.val.length = nums.val.length)
    (hscale : ∀ t (ht : t < nums.val.length),
      (v.val[t]'(by omega)).val = c * (nums.val[t]'ht).val)
    (hbounds_v : ∀ t (ht : t < v.val.length),
      -1000000 ≤ (v.val[t]'ht).val ∧ (v.val[t]'ht).val ≤ 1000000), ∀ r s : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        Aegis.SplitArray.split_array v = ok s → r = s) := by
  sorry

/-- The function returns true if and only if n >= 7 and n mod 4 = 3.
  Preconditions: Let n = len(nums). 1 <= n <= 2000. There exists an integer a with a != 0 and -1000000 <= a <= 1000000 such that nums[t] = a for every 0 <= t < n. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hconst : ∃ a : ℤ,
      a ≠ 0 ∧ -1000000 ≤ a ∧ a ≤ 1000000 ∧
        ∀ t (ht : t < nums.val.length), (nums.val[t]'ht).val = a) :
    ∀ r : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        (r = true ↔ 7 ≤ nums.val.length ∧ nums.val.length % 4 = 3) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_lower : 1 ≤ nums.val.length) (hn_upper : nums.val.length ≤ 2000)
    (hconst : ∃ a : ℤ,
      a ≠ 0 ∧ -1000000 ≤ a ∧ a ≤ 1000000 ∧
        ∀ t (ht : t < nums.val.length), (nums.val[t]'ht).val = a), ∀ r : Bool,
      Aegis.SplitArray.split_array nums = ok r →
        (r = true ↔ 7 ≤ nums.val.length ∧ nums.val.length % 4 = 3)) := by
  sorry

end AegisSpec.SplitArray
