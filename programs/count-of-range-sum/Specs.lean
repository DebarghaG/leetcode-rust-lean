import Aegis.CountRangeSum.Code.Funs

/-!
# Specifications of `Aegis.CountRangeSum.count_range_sum`

LeetCode problem `count-of-range-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountRangeSum

set_option autoImplicit false

namespace AegisSpec.CountRangeSum

def sliceInts (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def elem (nums : Slice Std.I64) (k : Nat) : Int := (sliceInts nums).getD k 0

def segSum (nums : Slice Std.I64) (i j : Nat) : Int :=
  (((sliceInts nums).drop i).take (j + 1 - i)).sum

def indexPairs (nums : Slice Std.I64) : Finset (Nat × Nat) :=
  ((Finset.range nums.val.length).product (Finset.range nums.val.length)).filter
    (fun p => p.1 ≤ p.2)

def countInRange (nums : Slice Std.I64) (lower upper : Int) : Nat :=
  ((indexPairs nums).filter
    (fun p => lower ≤ segSum nums p.1 p.2 ∧ segSum nums p.1 p.2 ≤ upper)).card

def countEqSum (nums : Slice Std.I64) (c : Int) : Nat :=
  ((indexPairs nums).filter (fun p => segSum nums p.1 p.2 = c)).card

def countSingles (nums : Slice Std.I64) (lower upper : Int) : Nat :=
  ((Finset.range nums.val.length).filter
    (fun k => lower ≤ elem nums k ∧ elem nums k ≤ upper)).card

def totalPairs (n : Nat) : Nat := n * (n + 1) / 2

def constCount (n : Nat) (c lower upper : Int) : Nat :=
  (Finset.range n).sum (fun k =>
    (n - k) * (if lower ≤ ((k : Int) + 1) * c ∧ ((k : Int) + 1) * c ≤ upper then 1 else 0))

def negI64 (x : Std.I64) : Std.I64 := (-x.bv)#iscalar

def sliceOfList (l : List Std.I64) (h : l.length ≤ Usize.max) : Slice Std.I64 where
  leng := l.length
  list := Data.ListN.ListN.fromList l
  bound := h

def reverseSlice (nums : Slice Std.I64) : Slice Std.I64 :=
  sliceOfList nums.val.reverse (by
    rw [List.length_reverse]
    have hv : nums.val.length = nums.leng := Data.ListN.ListN_length nums.list
    rw [hv]
    exact nums.bound)

def negSlice (nums : Slice Std.I64) : Slice Std.I64 :=
  sliceOfList (nums.val.map negI64) (by
    rw [List.length_map]
    have hv : nums.val.length = nums.leng := Data.ListN.ListN_length nums.list
    rw [hv]
    exact nums.bound)

/-- Whenever count_range_sum nums lower upper returns a result r, r is an i64 equal to the number of pairs (i,j) of integers with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper, where sum_{t=i}^j nums[t] is the ordinary mathematical sum of the elements nums[i], nums[i+1], ..., nums[j].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_1 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    r.val = ((countInRange nums lower.val upper.val : Nat) : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), r.val = ((countInRange nums lower.val upper.val : Nat) : Int)) := by
  sorry

/-- count_range_sum nums lower upper returns a result r; it does not fail.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_2 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1) :
    ∃ r : Std.I64, count_range_sum nums lower upper = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1), ∃ r : Std.I64, count_range_sum nums lower upper = Result.ok r) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, 0 <= r <= n*(n+1)/2, where n = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_3 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    0 ≤ r.val ∧ r.val ≤ ((totalPairs nums.val.length : Nat) : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), 0 ≤ r.val ∧ r.val ≤ ((totalPairs nums.val.length : Nat) : Int)) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r >= #{k | 0 <= k < n and lower <= nums[k] <= upper}, where n = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_4 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    ((countSingles nums lower.val upper.val : Nat) : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), ((countSingles nums lower.val upper.val : Nat) : Int) ≤ r.val) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r = 0 if and only if for every pair of integers (i,j) with 0 <= i <= j < n, the sum sum_{t=i}^j nums[t] is either less than lower or greater than upper. Equivalently, r > 0 if and only if at least one contiguous nonempty subarray sum lies in [lower, upper].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_5 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    (r.val = 0 ↔
      ∀ (i j : Nat), i ≤ j → j < nums.val.length →
        segSum nums i j < lower.val ∨ upper.val < segSum nums i j) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), (r.val = 0 ↔
      ∀ (i j : Nat), i ≤ j → j < nums.val.length →
        segSum nums i j < lower.val ∨ upper.val < segSum nums i j)) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r = 1 if lower <= nums[0] <= upper, and r = 0 otherwise.
  Preconditions: Let n = len(nums). Assume n = 1; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_6 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hn : nums.val.length = 1)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    r.val = if lower.val ≤ elem nums 0 ∧ elem nums 0 ≤ upper.val then 1 else 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hn : nums.val.length = 1)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), r.val = if lower.val ≤ elem nums 0 ∧ elem nums 0 ≤ upper.val then 1 else 0) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r equals the number of pairs (i,j) with 0 <= i <= j < n and sum_{t=i}^j nums[t] = lower.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower = upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_7 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hlower : lower.val = upper.val)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    r.val = ((countEqSum nums lower.val : Nat) : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hlower : lower.val = upper.val)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), r.val = ((countEqSum nums lower.val : Nat) : Int)) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r = n*(n+1)/2, where n = len(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; for every pair (i,j) with 0 <= i <= j < n, lower <= sum_{t=i}^j nums[t] <= upper; and the number of such pairs is at most 2^31-1. -/
theorem spec_8 (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hall : ∀ (i j : Nat), i ≤ j → j < nums.val.length →
      lower.val ≤ segSum nums i j ∧ segSum nums i j ≤ upper.val)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    r.val = ((totalPairs nums.val.length : Nat) : Int) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hall : ∀ (i j : Nat), i ≤ j → j < nums.val.length →
      lower.val ≤ segSum nums i j ∧ segSum nums i j ≤ upper.val)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), r.val = ((totalPairs nums.val.length : Nat) : Int)) := by
  sorry

/-- If count_range_sum nums lower1 upper1 returns a result r1 and count_range_sum nums lower2 upper2 returns a result r2, then r1 <= r2.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower1 <= upper1 <= 100000; -100000 <= lower2 <= upper2 <= 100000; lower2 <= lower1; upper1 <= upper2; the number of pairs (i,j) with 0 <= i <= j < n and lower1 <= sum_{t=i}^j nums[t] <= upper1 is at most 2^31-1; and the number of pairs (i,j) with 0 <= i <= j < n and lower2 <= sum_{t=i}^j nums[t] <= upper2 is at most 2^31-1. -/
theorem spec_9 (nums : Slice Std.I64)
    (lower1 upper1 lower2 upper2 r1 r2 : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds1 : -(100000 : Int) ≤ lower1.val ∧ lower1.val ≤ upper1.val ∧
      upper1.val ≤ 100000)
    (hbounds2 : -(100000 : Int) ≤ lower2.val ∧ lower2.val ≤ upper2.val ∧
      upper2.val ≤ 100000)
    (hlo : lower2.val ≤ lower1.val)
    (hup : upper1.val ≤ upper2.val)
    (hcount1 : countInRange nums lower1.val upper1.val ≤ 2 ^ 31 - 1)
    (hcount2 : countInRange nums lower2.val upper2.val ≤ 2 ^ 31 - 1)
    (hres1 : count_range_sum nums lower1 upper1 = Result.ok r1)
    (hres2 : count_range_sum nums lower2 upper2 = Result.ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (lower1 upper1 lower2 upper2 r1 r2 : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds1 : -(100000 : Int) ≤ lower1.val ∧ lower1.val ≤ upper1.val ∧
      upper1.val ≤ 100000)
    (hbounds2 : -(100000 : Int) ≤ lower2.val ∧ lower2.val ≤ upper2.val ∧
      upper2.val ≤ 100000)
    (hlo : lower2.val ≤ lower1.val)
    (hup : upper1.val ≤ upper2.val)
    (hcount1 : countInRange nums lower1.val upper1.val ≤ 2 ^ 31 - 1)
    (hcount2 : countInRange nums lower2.val upper2.val ≤ 2 ^ 31 - 1)
    (hres1 : count_range_sum nums lower1 upper1 = Result.ok r1)
    (hres2 : count_range_sum nums lower2 upper2 = Result.ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If count_range_sum nums lower upper returns a result r and count_range_sum rev lower upper returns a result r', then r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. Let rev be the slice of length n with rev[k] = nums[n-1-k] for 0 <= k < n. -/
theorem spec_10 (nums : Slice Std.I64) (lower upper r r' : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r)
    (hres' : count_range_sum (reverseSlice nums) lower upper = Result.ok r') :
    r.val = r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r r' : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r)
    (hres' : count_range_sum (reverseSlice nums) lower upper = Result.ok r'), r.val = r'.val) := by
  sorry

/-- Whenever count_range_sum nums lower upper returns a result r, r = sum_{L=1}^{n} (n-L+1) * I(L), where for each L, I(L) = 1 if lower <= L*c <= upper and I(L) = 0 otherwise.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; there is an integer c such that nums[k] = c for every 0 <= k < n; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. -/
theorem spec_11 (nums : Slice Std.I64) (lower upper r : Std.I64) (c : Int)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hconst : ∀ (k : Nat), k < nums.val.length → elem nums k = c)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r) :
    r.val = ((constCount nums.val.length c lower.val upper.val : Nat) : Int) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r : Std.I64) (c : Int)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hconst : ∀ (k : Nat), k < nums.val.length → elem nums k = c)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r), r.val = ((constCount nums.val.length c lower.val upper.val : Nat) : Int)) := by
  sorry

/-- If count_range_sum nums lower upper returns a result r and count_range_sum negnums (-upper) (-lower) returns a result r', then r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000; for every k with 0 <= k < n, -2^31 <= nums[k] <= 2^31-1; -100000 <= lower <= upper <= 100000; and the number of pairs (i,j) with 0 <= i <= j < n and lower <= sum_{t=i}^j nums[t] <= upper is at most 2^31-1. Let negnums be the slice of length n with negnums[k] = -nums[k] for 0 <= k < n. Assume additionally that negnums also satisfies the nums bounds, equivalently -2^31 <= -nums[k] <= 2^31-1 for every k, i.e. nums[k] >= -2^31+1. -/
theorem spec_12 (nums : Slice Std.I64) (lower upper r r' : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hnegnums : ∀ (k : Nat), k < nums.val.length →
      -((2 ^ 31 : Int)) + 1 ≤ elem nums k)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r)
    (hres' : count_range_sum (negSlice nums) (negI64 upper) (negI64 lower) =
      Result.ok r') :
    r.val = r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper r r' : Std.I64)
    (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000)
    (hnums : ∀ (k : Nat), k < nums.val.length →
      -(2 ^ 31 : Int) ≤ elem nums k ∧ elem nums k ≤ 2 ^ 31 - 1)
    (hbounds : -(100000 : Int) ≤ lower.val ∧ lower.val ≤ upper.val ∧ upper.val ≤ 100000)
    (hnegnums : ∀ (k : Nat), k < nums.val.length →
      -((2 ^ 31 : Int)) + 1 ≤ elem nums k)
    (hcount : countInRange nums lower.val upper.val ≤ 2 ^ 31 - 1)
    (hres : count_range_sum nums lower upper = Result.ok r)
    (hres' : count_range_sum (negSlice nums) (negI64 upper) (negI64 lower) =
      Result.ok r'), r.val = r'.val) := by
  sorry

end AegisSpec.CountRangeSum
