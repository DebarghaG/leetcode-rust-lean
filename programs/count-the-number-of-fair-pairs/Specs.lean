import Aegis.CountFairPairs.Code.Funs

/-!
# Specifications of `Aegis.CountFairPairs.count_fair_pairs`

LeetCode problem `count-the-number-of-fair-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.CountFairPairs

namespace AegisSpec.CountFairPairs

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def i64 (x : ℤ) : Std.I64 := ⟨BitVec.ofInt 64 x⟩

def pairSum (l : List ℤ) (i j : ℕ) : ℤ := l.getD i 0 + l.getD j 0

def fairPairCount (l : List ℤ) (lower upper : ℤ) : ℕ :=
  (((Finset.range l.length).product (Finset.range l.length)).filter
      (fun p : ℕ × ℕ =>
        p.1 < p.2 ∧ lower ≤ pairSum l p.1 p.2 ∧ pairSum l p.1 p.2 ≤ upper)).card

def eqSumPairCount (l : List ℤ) (s : ℤ) : ℕ := fairPairCount l s s

def ForAllPairs (l : List ℤ) (P : ℤ → ℤ → Prop) : Prop :=
  ∀ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j →
    P (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩)

def ExistsPair (l : List ℤ) (P : ℤ → ℤ → Prop) : Prop :=
  ∃ (i j : ℕ) (hi : i < l.length) (hj : j < l.length), i < j ∧
    P (l.get ⟨i, hi⟩) (l.get ⟨j, hj⟩)

def lengthOk (nums : Slice Std.I64) : Prop := 1 ≤ nums.val.length ∧ nums.val.length ≤ 100000

def elemsOk (nums : Slice Std.I64) : Prop :=
  ∀ x ∈ nums.val, -1000000000 ≤ x.val ∧ x.val ≤ 1000000000

/-- Whenever count_fair_pairs(nums, lower, upper) returns a result r, r equals the number of pairs (i, j) such that 0 <= i < j < len(nums) and lower <= nums[i] + nums[j] <= upper.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    r.val = (fairPairCount (vals nums) lower.val upper.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), r.val = (fairPairCount (vals nums) lower.val upper.val : ℤ)) := by
  sorry

/-- For every nums, lower, and upper satisfying the preconditions, count_fair_pairs(nums, lower, upper) returns a result r; it does not fail by overflow, panic, or out-of-bounds access.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000) :
    ∃ r : Std.I64, count_fair_pairs nums lower upper = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000), ∃ r : Std.I64, count_fair_pairs nums lower upper = ok r) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns a result r, 0 <= r <= len(nums) * (len(nums) - 1) / 2.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    0 ≤ r.val ∧ r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), 0 ≤ r.val ∧ r.val ≤ ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ)) := by
  sorry

/-- Whenever count_fair_pairs(nums, l1, u1) returns r1 and count_fair_pairs(nums, l2, u2) returns r2, r2 <= r1.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= l1 <= l2 <= u2 <= u1 <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64) (l1 l2 u2 u1 : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hl1 : -1000000000 ≤ l1.val) (h12 : l1.val ≤ l2.val) (h2u : l2.val ≤ u2.val)
    (hu21 : u2.val ≤ u1.val) (hu1 : u1.val ≤ 1000000000)
    (r1 r2 : Std.I64)
    (hr1 : count_fair_pairs nums l1 u1 = ok r1)
    (hr2 : count_fair_pairs nums l2 u2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (l1 l2 u2 u1 : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hl1 : -1000000000 ≤ l1.val) (h12 : l1.val ≤ l2.val) (h2u : l2.val ≤ u2.val)
    (hu21 : u2.val ≤ u1.val) (hu1 : u1.val ≤ 1000000000)
    (r1 r2 : Std.I64)
    (hr1 : count_fair_pairs nums l1 u1 = ok r1)
    (hr2 : count_fair_pairs nums l2 u2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r, count_fair_pairs(nums, lower, mid) returns r1, and count_fair_pairs(nums, mid + 1, upper) returns r2, we have r = r1 + r2.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; for an integer mid, -1000000000 <= lower <= mid < upper <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64) (lower upper mid : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hm1 : lower.val ≤ mid.val)
    (hm2 : mid.val < upper.val) (hupper : upper.val ≤ 1000000000)
    (r r1 r2 : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr1 : count_fair_pairs nums lower mid = ok r1)
    (hr2 : count_fair_pairs nums (i64 (mid.val + 1)) upper = ok r2) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper mid : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hm1 : lower.val ≤ mid.val)
    (hm2 : mid.val < upper.val) (hupper : upper.val ≤ 1000000000)
    (r r1 r2 : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr1 : count_fair_pairs nums lower mid = ok r1)
    (hr2 : count_fair_pairs nums (i64 (mid.val + 1)) upper = ok r2), r.val = r1.val + r2.val) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r and count_fair_pairs(nums', lower', upper') returns r', r = r'.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. Let nums' be the slice with len(nums') = len(nums) and nums'[i] = -nums[i] for every i; let lower' = -upper and upper' = -lower. -/
theorem spec_6 (nums nums' : Slice Std.I64) (lower upper lower' upper' : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hnums' : vals nums' = (vals nums).map (fun x => -x))
    (hlower' : lower'.val = -upper.val) (hupper' : upper'.val = -lower.val)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums' lower' upper' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (lower upper lower' upper' : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hnums' : vals nums' = (vals nums).map (fun x => -x))
    (hlower' : lower'.val = -upper.val) (hupper' : upper'.val = -lower.val)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums' lower' upper' = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r and count_fair_pairs(nums', lower, upper) returns r', r = r'.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. Let nums' be a slice with the same length as nums that is a permutation of nums: there is a bijection p from {0,...,len(nums)-1} to itself with nums'[i] = nums[p(i)] for every i. -/
theorem spec_7 (nums nums' : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hperm : ∃ p : Equiv.Perm (Fin nums.val.length),
      nums'.val = List.ofFn (fun i => nums.val.get (p i)))
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums' lower upper = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hperm : ∃ p : Equiv.Perm (Fin nums.val.length),
      nums'.val = List.ofFn (fun i => nums.val.get (p i)))
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums' lower upper = ok r'), r.val = r'.val) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r, r > 0 if and only if there exist indices i and j with 0 <= i < j < len(nums) and lower <= nums[i] + nums[j] <= upper.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    0 < r.val ↔
      ExistsPair (vals nums) (fun a b => lower.val ≤ a + b ∧ a + b ≤ upper.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), 0 < r.val ↔
      ExistsPair (vals nums) (fun a b => lower.val ≤ a + b ∧ a + b ≤ upper.val)) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r, r = 0.
  Preconditions: len(nums) is between 1 and 100000 inclusive; len(nums) = 1; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_9 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (hlen1 : nums.val.length = 1) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    r.val = 0 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (hlen1 : nums.val.length = 1) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), r.val = 0) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r, if lower <= 2 * v <= upper then r = len(nums) * (len(nums) - 1) / 2, and otherwise r = 0.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. There is an integer v such that nums[i] = v for every i with 0 <= i < len(nums). -/
theorem spec_10 (nums : Slice Std.I64) (lower upper : Std.I64) (v : ℤ)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hall : vals nums = List.replicate nums.val.length v)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    r.val = if lower.val ≤ 2 * v ∧ 2 * v ≤ upper.val
      then ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) else 0 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64) (v : ℤ)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (hall : vals nums = List.replicate nums.val.length v)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), r.val = if lower.val ≤ 2 * v ∧ 2 * v ≤ upper.val
      then ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) else 0) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r, r = len(nums) * (len(nums) - 1) / 2 if and only if for every i and j with 0 <= i < j < len(nums), lower <= nums[i] + nums[j] <= upper.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower <= upper <= 1000000000. -/
theorem spec_11 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r) :
    r.val = ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) ↔
      ForAllPairs (vals nums) (fun a b => lower.val ≤ a + b ∧ a + b ≤ upper.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hle : lower.val ≤ upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r : Std.I64) (hr : count_fair_pairs nums lower upper = ok r), r.val = ((nums.val.length * (nums.val.length - 1) / 2 : ℕ) : ℤ) ↔
      ForAllPairs (vals nums) (fun a b => lower.val ≤ a + b ∧ a + b ≤ upper.val)) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r and count_fair_pairs(nums, lower, upper - 1) returns r', r - r' equals the number of pairs (i, j) such that 0 <= i < j < len(nums) and nums[i] + nums[j] = upper.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower < upper <= 1000000000. -/
theorem spec_12 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hlu : lower.val < upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums lower (i64 (upper.val - 1)) = ok r') :
    r.val - r'.val = (eqSumPairCount (vals nums) upper.val : ℤ) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hlu : lower.val < upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums lower (i64 (upper.val - 1)) = ok r'), r.val - r'.val = (eqSumPairCount (vals nums) upper.val : ℤ)) := by
  sorry

/-- Whenever count_fair_pairs(nums, lower, upper) returns r and count_fair_pairs(nums, lower + 1, upper) returns r', r - r' equals the number of pairs (i, j) such that 0 <= i < j < len(nums) and nums[i] + nums[j] = lower.
  Preconditions: len(nums) is between 1 and 100000 inclusive; for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000; -1000000000 <= lower < upper <= 1000000000. -/
theorem spec_13 (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hlu : lower.val < upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums (i64 (lower.val + 1)) upper = ok r') :
    r.val - r'.val = (eqSumPairCount (vals nums) lower.val : ℤ) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (lower upper : Std.I64)
    (hlen : lengthOk nums) (helems : elemsOk nums)
    (hlower : -1000000000 ≤ lower.val) (hlu : lower.val < upper.val)
    (hupper : upper.val ≤ 1000000000)
    (r r' : Std.I64)
    (hr : count_fair_pairs nums lower upper = ok r)
    (hr' : count_fair_pairs nums (i64 (lower.val + 1)) upper = ok r'), r.val - r'.val = (eqSumPairCount (vals nums) lower.val : ℤ)) := by
  sorry

end AegisSpec.CountFairPairs
