import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `divide-an-array-into-subarrays-with-minimum-cost-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinimumCost

namespace AegisSpec.MinimumCost

def elem (l : List Std.I64) (i : ℕ) : ℤ :=
  match l[i]? with
  | some x => x.val
  | none => 0

def splitCost (l : List Std.I64) (i j : ℕ) : ℤ := elem l 0 + elem l i + elem l j

def IsMinSplitCost (l : List Std.I64) (r : ℤ) : Prop :=
  (∃ i j, 1 ≤ i ∧ i < j ∧ j < l.length ∧ r = splitCost l i j) ∧
    (∀ i j, 1 ≤ i → i < j → j < l.length → r ≤ splitCost l i j)

def IsTwoSmallestTail (l : List Std.I64) (a b : ℤ) : Prop :=
  (∃ i j, 1 ≤ i ∧ i < j ∧ j < l.length ∧ elem l i = a ∧ elem l j = b) ∧
    (∀ p q, 1 ≤ p → p < q → q < l.length → a + b ≤ elem l p + elem l q)

def total (l : List Std.I64) : ℤ := (l.map (fun x => x.val)).sum

/-- Whenever the function returns a result r, r is the minimum possible total cost of a division of nums into three disjoint nonempty contiguous subarrays that cover nums in order. Equivalently, r = min { nums[0] + nums[i] + nums[j] | 1 ≤ i < j < n }, where i is the 0-based start index of the second subarray and j is the 0-based start index of the third subarray.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r → IsMinSplitCost nums.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r → IsMinSplitCost nums.val r.val) := by
  sorry

/-- Under these preconditions, the function returns a result r; that is, it does not fail, panic, or overflow.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∃ (r : Std.I64), minimum_cost nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∃ (r : Std.I64), minimum_cost nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exist integers i and j such that 1 ≤ i < j < n and r = nums[0] + nums[i] + nums[j]. Equivalently, some division of nums into three nonempty contiguous subarrays has total cost exactly r.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∃ i j, 1 ≤ i ∧ i < j ∧ j < nums.val.length ∧ r.val = splitCost nums.val i j := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∃ i j, 1 ≤ i ∧ i < j ∧ j < nums.val.length ∧ r.val = splitCost nums.val i j) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers i and j with 1 ≤ i < j < n, we have r ≤ nums[0] + nums[i] + nums[j].
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_4 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∀ i j, 1 ≤ i → i < j → j < nums.val.length → r.val ≤ splitCost nums.val i j := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∀ i j, 1 ≤ i → i < j → j < nums.val.length → r.val ≤ splitCost nums.val i j) := by
  sorry

/-- Whenever the function returns a result r, r ≥ nums[0] + 2.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_5 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r → elem nums.val 0 + 2 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r → elem nums.val 0 + 2 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r ≤ nums[0] + 100.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r → r.val ≤ elem nums.val 0 + 100 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r → r.val ≤ elem nums.val 0 + 100) := by
  sorry

/-- Let a and b be the two smallest values among nums[1], nums[2], ..., nums[n-1], counted with multiplicity at two distinct positions. Whenever the function returns a result r, r = nums[0] + a + b.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∀ a b, IsTwoSmallestTail nums.val a b → r.val = elem nums.val 0 + a + b := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∀ a b, IsTwoSmallestTail nums.val a b → r.val = elem nums.val 0 + a + b) := by
  sorry

/-- If the function returns r on input nums and returns r' on input nums', then r = r'.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and 1 ≤ nums[i] ≤ 50 for 0 ≤ i < n. Let nums' be another slice with len(nums') = n, satisfying 1 ≤ nums'[i] ≤ 50 for all i, such that nums'[0] = nums[0] and the multiset of entries nums'[1], ..., nums'[n-1] equals the multiset of entries nums[1], ..., nums[n-1]. -/
theorem spec_8 (nums nums' : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50)
    (hrange' : ∀ i, i < nums'.val.length → 1 ≤ elem nums'.val i ∧ elem nums'.val i ≤ 50)
    (hlen : nums'.val.length = nums.val.length)
    (hfirst : elem nums'.val 0 = elem nums.val 0)
    (hperm : (nums'.val.drop 1).Perm (nums.val.drop 1)) :
    ∀ (r r' : Std.I64), minimum_cost nums = ok r → minimum_cost nums' = ok r' →
      r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50)
    (hrange' : ∀ i, i < nums'.val.length → 1 ≤ elem nums'.val i ∧ elem nums'.val i ≤ 50)
    (hlen : nums'.val.length = nums.val.length)
    (hfirst : elem nums'.val 0 = elem nums.val 0)
    (hperm : (nums'.val.drop 1).Perm (nums.val.drop 1)), ∀ (r r' : Std.I64), minimum_cost nums = ok r → minimum_cost nums' = ok r' →
      r.val = r'.val) := by
  sorry

/-- Whenever the function returns a result r, r is at least the minimum value of nums[a] + nums[b] + nums[c] over all triples of distinct indices a, b, c with 0 ≤ a < b < c < n.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∃ a b c, a < b ∧ b < c ∧ c < nums.val.length ∧
        elem nums.val a + elem nums.val b + elem nums.val c ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r →
      ∃ a b c, a < b ∧ b < c ∧ c < nums.val.length ∧
        elem nums.val a + elem nums.val b + elem nums.val c ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r ≤ sum_{i=0}^{n-1} nums[i].
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and, for every i with 0 ≤ i < n, 1 ≤ nums[i] ≤ 50. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50) :
    ∀ (r : Std.I64), minimum_cost nums = ok r → r.val ≤ total nums.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50), ∀ (r : Std.I64), minimum_cost nums = ok r → r.val ≤ total nums.val) := by
  sorry

/-- If the function returns r on input nums and returns r' on input nums', then r' = r + 3c.
  Preconditions: Let n = len(nums). Assume 3 ≤ n ≤ 50 and 1 ≤ nums[i] ≤ 50 for 0 ≤ i < n. Let c be an integer such that 1 ≤ nums[i] + c ≤ 50 for all i, and let nums' be the slice with nums'[i] = nums[i] + c for all 0 ≤ i < n. -/
theorem spec_11 (nums nums' : Slice Std.I64) (c : ℤ)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50)
    (hc : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i + c ∧ elem nums.val i + c ≤ 50)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i, i < nums.val.length → elem nums'.val i = elem nums.val i + c) :
    ∀ (r r' : Std.I64), minimum_cost nums = ok r → minimum_cost nums' = ok r' →
      r'.val = r.val + 3 * c := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (c : ℤ)
    (hn3 : 3 ≤ nums.val.length) (hn50 : nums.val.length ≤ 50)
    (hrange : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i ∧ elem nums.val i ≤ 50)
    (hc : ∀ i, i < nums.val.length → 1 ≤ elem nums.val i + c ∧ elem nums.val i + c ≤ 50)
    (hlen : nums'.val.length = nums.val.length)
    (hshift : ∀ i, i < nums.val.length → elem nums'.val i = elem nums.val i + c), ∀ (r r' : Std.I64), minimum_cost nums = ok r → minimum_cost nums' = ok r' →
      r'.val = r.val + 3 * c) := by
  sorry

end AegisSpec.MinimumCost
