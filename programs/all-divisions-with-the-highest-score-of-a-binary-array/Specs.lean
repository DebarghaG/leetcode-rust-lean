import Aegis.MaxScoreIndices.Code.Funs

/-!
# Specifications of `Aegis.MaxScoreIndices.max_score_indices`

LeetCode problem `all-divisions-with-the-highest-score-of-a-binary-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxScoreIndices

def isBinaryList (l : List Std.I64) : Prop :=
  ∀ v ∈ l, v.val = 0 ∨ v.val = 1

def divisionScore (l : List Std.I64) (i : ℕ) : ℕ :=
  (l.take i).countP (fun v => v.val = 0) + (l.drop i).countP (fun v => v.val = 1)

def maxDivisionScore (l : List Std.I64) : ℕ :=
  (List.range (l.length + 1)).foldr
    (fun k acc => max (divisionScore l k) acc) (divisionScore l 0)

def Occurs (x : ℤ) (r : alloc.vec.Vec Std.I64) : Prop :=
  ∃ v ∈ r.val, v.val = x

/-- Whenever the function returns a result r, the following holds: for every i64 value x, x occurs in r if and only if 0 <= x <= n and S(x) = M; and no value occurs more than once in r. Here x occurs in r means there exists k with 0 <= k < len(r) and r[k] = x. Equivalently, r contains exactly all division indices whose division score is the maximum M, in any order and without duplicates.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every j with 0 <= j < n, nums[j] is either 0 or 1. For each integer i with 0 <= i <= n define S(i) = (number of j with 0 <= j < i and nums[j] = 0) + (number of j with i <= j < n and nums[j] = 1), and let M = max_{0 <= k <= n} S(k). -/
theorem spec_1 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hbound : nums.val.length ≤ 100000)
    (hbin : isBinaryList nums.val) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxScoreIndices.max_score_indices nums = Result.ok r →
        (∀ x : ℤ,
          Occurs x r ↔
            0 ≤ x ∧ x ≤ (nums.val.length : ℤ) ∧
              divisionScore nums.val x.toNat = maxDivisionScore nums.val) ∧
          r.val.Nodup := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hbound : nums.val.length ≤ 100000)
    (hbin : isBinaryList nums.val), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MaxScoreIndices.max_score_indices nums = Result.ok r →
        (∀ x : ℤ,
          Occurs x r ↔
            0 ≤ x ∧ x ≤ (nums.val.length : ℤ) ∧
              divisionScore nums.val x.toNat = maxDivisionScore nums.val) ∧
          r.val.Nodup) := by
  sorry

/-- For every valid input, the function returns a result r; it does not fail by overflow, out-of-bounds access, or panic.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every j with 0 <= j < n, nums[j] is either 0 or 1. -/
theorem spec_2 (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hbound : nums.val.length ≤ 100000)
    (hbin : isBinaryList nums.val) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxScoreIndices.max_score_indices nums = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hpos : 1 ≤ nums.val.length)
    (hbound : nums.val.length ≤ 100000)
    (hbin : isBinaryList nums.val), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MaxScoreIndices.max_score_indices nums = Result.ok r) := by
  sorry

end AegisSpec.MaxScoreIndices
