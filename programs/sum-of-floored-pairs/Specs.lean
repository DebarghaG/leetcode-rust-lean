import Aegis.SumOfFlooredPairs.Code.Funs

/-!
# Specifications of `Aegis.SumOfFlooredPairs.sum_of_floored_pairs`

LeetCode problem `sum-of-floored-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumOfFlooredPairs

def M : Int := 1000000007

def vals (nums : Slice Std.I64) : List Int := nums.val.map (fun x => x.val)

def pairTotal (l : List Int) : Int :=
  ((List.range l.length).map fun i =>
    ((List.range l.length).map fun j => l.getD i 0 / l.getD j 0).sum).sum

def S (nums : Slice Std.I64) : Int := pairTotal (vals nums)

def offDiagTotal (l : List Int) : Int :=
  ((List.range l.length).map fun i =>
    ((List.range l.length).map fun j => if i = j then 0 else l.getD i 0 / l.getD j 0).sum).sum

def T (nums : Slice Std.I64) : Int := offDiagTotal (vals nums)

def offDiagGeTotal (l : List Int) : Int :=
  ((List.range l.length).map fun i =>
    ((List.range l.length).map fun j =>
      if i = j then 0 else if l.getD j 0 ≤ l.getD i 0 then l.getD i 0 / l.getD j 0 else 0).sum).sum

def Tge (nums : Slice Std.I64) : Int := offDiagGeTotal (vals nums)

def count (l : List Int) (v : Int) : Nat := (l.filter (fun x => decide (x = v))).length

def distinctVals (l : List Int) : List Int := l.dedup

def weightedTotal (l : List Int) : Int :=
  ((distinctVals l).map fun u =>
    ((distinctVals l).map fun v =>
      (count l u : Int) * (count l v : Int) * (u / v)).sum).sum

def W (nums : Slice Std.I64) : Int := weightedTotal (vals nums)

/-- Whenever sum_of_floored_pairs(nums) returns a result r, there exists an integer q with q >= 0 such that S(nums) = q * M + r and 0 <= r < M. Equivalently, r is the unique canonical residue S(nums) mod M, namely the remainder of the total sum over all ordered pairs (i,j), including i=j, after division by M.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007. Define S(nums) = sum over all ordered index pairs (i,j) with 0 <= i < n and 0 <= j < n of floor(nums[i] / nums[j]), where floor is ordinary integer division of positive integers; the diagonal pairs i=j are included. -/
theorem spec_1 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      ∃ q : Int, 0 ≤ q ∧ S nums = q * M + r.val ∧ 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      ∃ q : Int, 0 ≤ q ∧ S nums = q * M + r.val ∧ 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- For every nums satisfying the preconditions, sum_of_floored_pairs(nums) returns some result r. It does not fail by arithmetic overflow, division by zero, out-of-bounds indexing, or panic.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∃ r : Std.I64, Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∃ r : Std.I64, Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r) := by
  sorry

/-- Whenever sum_of_floored_pairs(nums) returns r, r is a nonnegative integer strictly less than M, and moreover r <= S(nums). Thus the returned value is never negative, never reaches M, and never exceeds the true unmodded sum.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007 and let S(nums) be the unmodded ordered-pair total defined in spec_1. -/
theorem spec_3 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      0 ≤ r.val ∧ r.val < M ∧ r.val ≤ S nums := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      0 ≤ r.val ∧ r.val < M ∧ r.val ≤ S nums) := by
  sorry

/-- Let nums' be any slice that is a permutation of nums: len(nums') = n and there is a bijection pi on the indices {0,...,n-1} such that nums'[i] = nums[pi(i)] for every i. If sum_of_floored_pairs(nums) returns r and sum_of_floored_pairs(nums') returns r', then r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums nums' : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hperm : nums'.val.Perm nums.val) :
    ∀ (r r' : Std.I64),
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hperm : nums'.val.Perm nums.val), ∀ (r r' : Std.I64),
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Let k >= 1 be an integer and let nums' be a slice with len(nums') = n such that nums'[i] = k * nums[i] for every i and 1 <= nums'[i] <= 100000 for every i. If sum_of_floored_pairs(nums) returns r and sum_of_floored_pairs(nums') returns r', then r = r'.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_5 (nums nums' : Slice Std.I64) (k : Int)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hk : 1 ≤ k)
    (hlen' : nums'.val.length = nums.val.length)
    (hmul : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums'.val.get ⟨i, by rw [hlen']; exact hi⟩).val = k * (nums.val.get ⟨i, hi⟩).val)
    (hval' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r r' : Std.I64),
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Int)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hk : 1 ≤ k)
    (hlen' : nums'.val.length = nums.val.length)
    (hmul : ∀ (i : Nat) (hi : i < nums.val.length),
      (nums'.val.get ⟨i, by rw [hlen']; exact hi⟩).val = k * (nums.val.get ⟨i, hi⟩).val)
    (hval' : ∀ (i : Nat) (hi : i < nums'.val.length),
      1 ≤ (nums'.val.get ⟨i, hi⟩).val ∧ (nums'.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r r' : Std.I64),
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums' = ok r' → r.val = r'.val) := by
  sorry

/-- If S(nums) < M, then whenever sum_of_floored_pairs(nums) returns r, r = S(nums). In particular, under this condition r >= n.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007 and let S(nums) be the unmodded ordered-pair total defined in spec_1. -/
theorem spec_6 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hS : S nums < M) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      r.val = S nums ∧ (nums.val.length : Int) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hS : S nums < M), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      r.val = S nums ∧ (nums.val.length : Int) ≤ r.val) := by
  sorry

/-- If S(nums) >= M, then whenever sum_of_floored_pairs(nums) returns r, there is an integer q with q >= 1 such that S(nums) = q * M + r and 0 <= r < M. Equivalently, r is the remainder after subtracting floor(S(nums) / M) copies of M from S(nums).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007 and let S(nums) be the unmodded ordered-pair total defined in spec_1. -/
theorem spec_7 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hS : M ≤ S nums) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      ∃ q : Int, 1 ≤ q ∧ S nums = q * M + r.val ∧ 0 ≤ r.val ∧ r.val < M := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000)
    (hS : M ≤ S nums), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      ∃ q : Int, 1 ≤ q ∧ S nums = q * M + r.val ∧ 0 ≤ r.val ∧ r.val < M) := by
  sorry

/-- Whenever sum_of_floored_pairs(nums) returns r, r is congruent modulo M to n + T(nums), where T(nums) = sum over ordered pairs (i,j) with 0 <= i,j < n and i != j of floor(nums[i] / nums[j]). That is, r is congruent modulo M to the diagonal contribution n plus the off-diagonal ordered-pair total.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007. -/
theorem spec_8 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val ((nums.val.length : Int) + T nums) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val ((nums.val.length : Int) + T nums)) := by
  sorry

/-- Whenever sum_of_floored_pairs(nums) returns r, r is congruent modulo M to n + sum over ordered pairs (i,j) with 0 <= i,j < n, i != j, and nums[i] >= nums[j] of floor(nums[i] / nums[j]).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007. -/
theorem spec_9 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val ((nums.val.length : Int) + Tge nums) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val ((nums.val.length : Int) + Tge nums)) := by
  sorry

/-- Let V be the set of distinct values appearing in nums, and for each v in V let c(v) be the number of indices i with 0 <= i < n and nums[i] = v. Whenever sum_of_floored_pairs(nums) returns r, r is congruent modulo M to the sum over all u in V and all v in V of c(u) * c(v) * floor(u / v).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let M = 1000000007. -/
theorem spec_10 (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000) :
    ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val (W nums) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 100000)
    (hval : ∀ (i : Nat) (hi : i < nums.val.length),
      1 ≤ (nums.val.get ⟨i, hi⟩).val ∧ (nums.val.get ⟨i, hi⟩).val ≤ 100000), ∀ (r : Std.I64), Aegis.SumOfFlooredPairs.sum_of_floored_pairs nums = ok r →
      Int.ModEq M r.val (W nums)) := by
  sorry

end AegisSpec.SumOfFlooredPairs
