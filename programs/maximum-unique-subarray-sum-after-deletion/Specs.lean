import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `maximum-unique-subarray-sum-after-deletion`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSum

def sliceVals (s : Slice Std.I64) : List ℤ := s.val.map (fun x => x.val)

def occursIn (v : ℤ) (s : Slice Std.I64) : Prop := ∃ x ∈ s.val, x.val = v

def distinctPosSum (s : Slice Std.I64) : ℤ :=
  ((sliceVals s).toFinset.filter (fun v => 1 ≤ v ∧ v ≤ 100)).sum (fun v => v)

def sumPositiveWithMultiplicity (s : Slice Std.I64) : ℤ :=
  ((s.val.filter (fun x => decide (0 < x.val))).map (fun x => x.val)).sum

def listMax (l : List ℤ) : ℤ := l.foldr max (-100)

def dropNonPositive (s : Slice Std.I64) : List Std.I64 :=
  s.val.filter (fun x => decide (0 < x.val))

/-- Whenever max_sum(nums) returns a result r, r is characterized as follows. If there exists an index j with 0 <= j < len(nums) and nums[j] > 0, then r is the sum of all integers v such that 1 <= v <= 100 and v occurs in nums (each distinct positive value is counted exactly once). Otherwise, when no element of nums is positive, r is the maximum of the set {nums[i] | 0 <= i < len(nums)}.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_1 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    ((∃ x ∈ nums.val, 0 < x.val) → r.val = distinctPosSum nums) ∧
      ((∀ x ∈ nums.val, x.val ≤ 0) → r.val = listMax (sliceVals nums)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), ((∃ x ∈ nums.val, 0 < x.val) → r.val = distinctPosSum nums) ∧
      ((∀ x ∈ nums.val, x.val ≤ 0) → r.val = listMax (sliceVals nums))) := by
  sorry

/-- max_sum(nums) returns a result r; it does not fail for any input satisfying the preconditions.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_2 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100) :
    ∃ r : Std.I64, Aegis.MaxSum.max_sum nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100), ∃ r : Std.I64, Aegis.MaxSum.max_sum nums = ok r) := by
  sorry

/-- Whenever max_sum(nums) returns a result r, -100 <= r <= 5050.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_3 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    -100 ≤ r.val ∧ r.val ≤ 5050 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), -100 ≤ r.val ∧ r.val ≤ 5050) := by
  sorry

/-- Whenever max_sum(nums) returns a result r, r >= max_{0 <= i < len(nums)} nums[i].
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_4 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    listMax (sliceVals nums) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), listMax (sliceVals nums) ≤ r.val) := by
  sorry

/-- Whenever max_sum(nums) returns a result r, r <= sum_{0 <= i < len(nums), nums[i] > 0} nums[i], where this sum counts positive elements with multiplicity and is 0 if no element is positive.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_5 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    r.val ≤ sumPositiveWithMultiplicity nums := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), r.val ≤ sumPositiveWithMultiplicity nums) := by
  sorry

/-- Whenever max_sum(nums) returns a result r, there exist indices i_0 < i_1 < ... < i_k for some k >= 0 such that 0 <= i_0, i_k < len(nums), the values nums[i_0], ..., nums[i_k] are pairwise distinct, and r = nums[i_0] + nums[i_1] + ... + nums[i_k].
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_6 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    ∃ ys : List ℤ,
      ys.Sublist (sliceVals nums) ∧ ys.Nodup ∧ ys ≠ [] ∧ r.val = ys.sum := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), ∃ ys : List ℤ,
      ys.Sublist (sliceVals nums) ∧ ys.Nodup ∧ ys ≠ [] ∧ r.val = ys.sum) := by
  sorry

/-- Whenever max_sum(nums) returns a result r, for every k >= 0 and every sequence of indices i_0 < i_1 < ... < i_k with 0 <= i_0 and i_k < len(nums) such that nums[i_0], ..., nums[i_k] are pairwise distinct, the sum nums[i_0] + nums[i_1] + ... + nums[i_k] is <= r.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums). -/
theorem spec_7 (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r) :
    ∀ ys : List ℤ, ys.Sublist (sliceVals nums) → ys.Nodup → ys ≠ [] → ys.sum ≤ r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (r : Std.I64) (hr : Aegis.MaxSum.max_sum nums = ok r), ∀ ys : List ℤ, ys.Sublist (sliceVals nums) → ys.Nodup → ys ≠ [] → ys.sum ≤ r.val) := by
  sorry

/-- If max_sum(nums) returns r and max_sum(other) returns s, then r = s.
  Preconditions: nums and other are nonempty slices of 64-bit integers, each with length between 1 and 100 and every element between -100 and 100. For every integer v, v occurs in nums if and only if v occurs in other. -/
theorem spec_8 (nums other : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hne' : 1 ≤ other.length) (hle' : other.length ≤ 100)
    (hbounds' : ∀ x ∈ other.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hocc : ∀ v : ℤ, occursIn v nums ↔ occursIn v other)
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum nums = ok r) (hs : Aegis.MaxSum.max_sum other = ok s) :
    r = s := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums other : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hne' : 1 ≤ other.length) (hle' : other.length ≤ 100)
    (hbounds' : ∀ x ∈ other.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hocc : ∀ v : ℤ, occursIn v nums ↔ occursIn v other)
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum nums = ok r) (hs : Aegis.MaxSum.max_sum other = ok s), r = s) := by
  sorry

/-- If max_sum(nums) returns r and max_sum(xs) returns s, then r = s.
  Preconditions: nums is a nonempty slice of 64-bit integers with 1 <= len(nums) <= 100 and -100 <= nums[i] <= 100 for every i with 0 <= i < len(nums), and nums contains at least one positive element. Let xs be the slice obtained by deleting from nums every element nums[i] with nums[i] <= 0, preserving order. -/
theorem spec_9 (nums xs : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hpos : ∃ x ∈ nums.val, 0 < x.val)
    (hxs : xs.val = dropNonPositive nums)
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum nums = ok r) (hs : Aegis.MaxSum.max_sum xs = ok s) :
    r = s := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums xs : Slice Std.I64)
    (hne : 1 ≤ nums.length) (hle : nums.length ≤ 100)
    (hbounds : ∀ x ∈ nums.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hpos : ∃ x ∈ nums.val, 0 < x.val)
    (hxs : xs.val = dropNonPositive nums)
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum nums = ok r) (hs : Aegis.MaxSum.max_sum xs = ok s), r = s) := by
  sorry

/-- If max_sum(xs) returns r and max_sum(ys) returns s, then s = r + v.
  Preconditions: xs is a nonempty slice of 64-bit integers with 1 <= len(xs) <= 99 and -100 <= xs[i] <= 100 for every i with 0 <= i < len(xs), xs contains at least one positive element, v is an integer with 1 <= v <= 100, v does not occur in xs, and ys is the slice obtained by appending v to xs. -/
theorem spec_10 (xs ys : Slice Std.I64) (v : Std.I64)
    (hne : 1 ≤ xs.length) (hle : xs.length ≤ 99)
    (hbounds : ∀ x ∈ xs.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hpos : ∃ x ∈ xs.val, 0 < x.val)
    (hvlow : 1 ≤ v.val) (hvhigh : v.val ≤ 100)
    (hfresh : ¬ occursIn v.val xs)
    (hys : ys.val = xs.val ++ [v])
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum xs = ok r) (hs : Aegis.MaxSum.max_sum ys = ok s) :
    s.val = r.val + v.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (xs ys : Slice Std.I64) (v : Std.I64)
    (hne : 1 ≤ xs.length) (hle : xs.length ≤ 99)
    (hbounds : ∀ x ∈ xs.val, -100 ≤ x.val ∧ x.val ≤ 100)
    (hpos : ∃ x ∈ xs.val, 0 < x.val)
    (hvlow : 1 ≤ v.val) (hvhigh : v.val ≤ 100)
    (hfresh : ¬ occursIn v.val xs)
    (hys : ys.val = xs.val ++ [v])
    (r s : Std.I64)
    (hr : Aegis.MaxSum.max_sum xs = ok r) (hs : Aegis.MaxSum.max_sum ys = ok s), s.val = r.val + v.val) := by
  sorry

end AegisSpec.MaxSum
