import Aegis.SubArrayRanges.Code.Funs

/-!
# Specifications of `Aegis.SubArrayRanges.sub_array_ranges`

LeetCode problem `sum-of-subarray-ranges`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SubArrayRanges

namespace AegisSpec.SubArrayRanges

def ints (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def pairSum (n : ℕ) (f : ℕ → ℕ → ℤ) : ℤ :=
  (Finset.range n).sum (fun i => (Finset.Icc i (n - 1)).sum (fun j => f i j))

def seg (l : List ℤ) (i j : ℕ) : List ℤ := (l.drop i).take (j + 1 - i)

def valAt (l : List ℤ) (i : ℕ) : ℤ := l.getD i 0

def listMax : List ℤ → ℤ
  | [] => 0
  | x :: t => t.foldr max x

def listMin : List ℤ → ℤ
  | [] => 0
  | x :: t => t.foldr min x

def segMax (l : List ℤ) (i j : ℕ) : ℤ := listMax (seg l i j)

def segMin (l : List ℤ) (i j : ℕ) : ℤ := listMin (seg l i j)

/-- For every pair of indices i,j with 0 <= i <= j < n, let max(i,j) be the maximum of the set {nums[k] : i <= k <= j}, let min(i,j) be the minimum of the same set, and let R(i,j) = max(i,j) - min(i,j). Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = sum over all 0 <= i <= j < n of R(i,j).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length
        (fun i j => segMax (ints nums) i j - segMin (ints nums) i j) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length
        (fun i j => segMax (ints nums) i j - segMin (ints nums) i j)) := by
  sorry

/-- sub_array_ranges(nums) returns a result r; it does not panic, go out of bounds, or overflow.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∃ r : Std.I64, sub_array_ranges nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∃ r : Std.I64, sub_array_ranges nums = ok r) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r >= 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r → 0 ≤ r.val) := by
  sorry

/-- Let M = max {nums[k] : 0 <= k < n} and m = min {nums[k] : 0 <= k < n}. Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r >= M - m.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      segMax (ints nums) 0 (nums.val.length - 1) - segMin (ints nums) 0 (nums.val.length - 1)
        ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      segMax (ints nums) 0 (nums.val.length - 1) - segMin (ints nums) 0 (nums.val.length - 1)
        ≤ r.val) := by
  sorry

/-- Let M = max {nums[k] : 0 <= k < n} and m = min {nums[k] : 0 <= k < n}. Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r <= (n*(n-1)/2) * (M - m).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) *
        (segMax (ints nums) 0 (nums.val.length - 1) -
          segMin (ints nums) 0 (nums.val.length - 1)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) *
        (segMax (ints nums) 0 (nums.val.length - 1) -
          segMin (ints nums) 0 (nums.val.length - 1))) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = 0.
  Preconditions: len(nums) = 1 and -10^9 <= nums[0] <= 10^9. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hb : (-(10 ^ 9) : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 1)
    (hb : (-(10 ^ 9) : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r → r.val = 0) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = absolute_value(nums[0] - nums[1]).
  Preconditions: len(nums) = 2 and -10^9 <= nums[0] <= 10^9 and -10^9 <= nums[1] <= 10^9. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hb0 : (-(10 ^ 9) : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ (10 ^ 9 : ℤ))
    (hb1 : (-(10 ^ 9) : ℤ) ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = |(nums.val[0]).val - (nums.val[1]).val| := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen : nums.val.length = 2)
    (hb0 : (-(10 ^ 9) : ℤ) ≤ (nums.val[0]).val ∧ (nums.val[0]).val ≤ (10 ^ 9 : ℤ))
    (hb1 : (-(10 ^ 9) : ℤ) ≤ (nums.val[1]).val ∧ (nums.val[1]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = |(nums.val[0]).val - (nums.val[1]).val|) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = 0 if and only if all elements of nums are equal, that is, for every i,j with 0 <= i < n and 0 <= j < n, nums[i] = nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      (r.val = 0 ↔
        ∀ (i j : ℕ) (_hi : i < nums.val.length) (_hj : j < nums.val.length),
          (nums.val[i]).val = (nums.val[j]).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      (r.val = 0 ↔
        ∀ (i j : ℕ) (_hi : i < nums.val.length) (_hj : j < nums.val.length),
          (nums.val[i]).val = (nums.val[j]).val)) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = sum over all 0 <= i <= j < n of (nums[j] - nums[i]).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9, and nums is nondecreasing: for every i with 0 <= i < n-1, nums[i] <= nums[i+1]. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hmono : ∀ (i : ℕ) (_hi : i + 1 < nums.val.length),
      (nums.val[i]).val ≤ (nums.val[i + 1]).val) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length
        (fun i j => valAt (ints nums) j - valAt (ints nums) i) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hmono : ∀ (i : ℕ) (_hi : i + 1 < nums.val.length),
      (nums.val[i]).val ≤ (nums.val[i + 1]).val), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length
        (fun i j => valAt (ints nums) j - valAt (ints nums) i)) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r and sub_array_ranges(rev) returns a result r', both regarded as integers, r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let rev be the array of length n with rev[i] = nums[n-1-i] for 0 <= i < n; then rev also has all entries in {-10^9,...,10^9}. -/
theorem spec_10 (nums rev : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hrev : rev.val = nums.val.reverse) :
    ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges rev = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums rev : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hrev : rev.val = nums.val.reverse), ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges rev = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r and sub_array_ranges(neg) returns a result r', both regarded as integers, r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let neg be the array of length n with neg[i] = -nums[i] for 0 <= i < n; then neg also has all entries in {-10^9,...,10^9}. -/
theorem spec_11 (nums neg : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hneg : ints neg = (ints nums).map (fun v => -v)) :
    ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges neg = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums neg : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hneg : ints neg = (ints nums).map (fun v => -v)), ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges neg = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r and sub_array_ranges(shifted) returns a result r', both regarded as integers, r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let c be an integer such that for every i with 0 <= i < n, -10^9 <= nums[i] + c <= 10^9, and let shifted be the array with shifted[i] = nums[i] + c. -/
theorem spec_12 (nums shifted : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hc : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ (10 ^ 9 : ℤ))
    (hshift : ints shifted = (ints nums).map (fun v => v + c)) :
    ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges shifted = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums shifted : Slice Std.I64) (c : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hc : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ (10 ^ 9 : ℤ))
    (hshift : ints shifted = (ints nums).map (fun v => v + c)), ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges shifted = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever sub_array_ranges(nums) returns a result r and sub_array_ranges(scaled) returns a result r', both regarded as integers, r' = k * r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. Let k be an integer with k >= 0 such that for every i with 0 <= i < n, -10^9 <= k*nums[i] <= 10^9, and let scaled be the array with scaled[i] = k*nums[i]. -/
theorem spec_13 (nums scaled : Slice Std.I64) (k : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hk : 0 ≤ k)
    (hkb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ k * (nums.val[i]).val ∧ k * (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hscale : ints scaled = (ints nums).map (fun v => k * v)) :
    ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges scaled = ok r' →
      r'.val = k * r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums scaled : Slice Std.I64) (k : ℤ)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hk : 0 ≤ k)
    (hkb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ k * (nums.val[i]).val ∧ k * (nums.val[i]).val ≤ (10 ^ 9 : ℤ))
    (hscale : ints scaled = (ints nums).map (fun v => k * v)), ∀ (r r' : Std.I64), sub_array_ranges nums = ok r → sub_array_ranges scaled = ok r' →
      r'.val = k * r.val) := by
  sorry

/-- For every 0 <= i <= j < n, define max(i,j) as the maximum of {nums[k] : i <= k <= j} and min(i,j) as the minimum of the same set. Whenever sub_array_ranges(nums) returns a result r, regarded as an integer, r = (sum over all 0 <= i <= j < n of max(i,j)) - (sum over all 0 <= i <= j < n of min(i,j)).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 1000 and, for every i with 0 <= i < n, -10^9 <= nums[i] <= 10^9. -/
theorem spec_14 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)) :
    ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length (fun i j => segMax (ints nums) i j) -
        pairSum nums.val.length (fun i j => segMin (ints nums) i j) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
    (hb : ∀ (i : ℕ) (_hi : i < nums.val.length),
      (-(10 ^ 9) : ℤ) ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ (10 ^ 9 : ℤ)), ∀ (r : Std.I64), sub_array_ranges nums = ok r →
      r.val = pairSum nums.val.length (fun i j => segMax (ints nums) i j) -
        pairSum nums.val.length (fun i j => segMin (ints nums) i j)) := by
  sorry

end AegisSpec.SubArrayRanges
