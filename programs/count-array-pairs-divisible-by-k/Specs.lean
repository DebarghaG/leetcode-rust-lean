import Aegis.CountPairs.Code.Funs

/-!
# Specifications of `Aegis.CountPairs.count_pairs`

LeetCode problem `count-array-pairs-divisible-by-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aegis.CountPairs

namespace AegisSpec.CountPairs

def DivisibleBy (k m : ℤ) : Prop := ∃ q : ℤ, m = q * k

def totalPairs (n : ℕ) : ℕ := n * (n - 1) / 2

noncomputable def numGoodPairs (l : List Std.I64) (k : Std.I64) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin l.length × Fin l.length =>
    p.1 < p.2 ∧ DivisibleBy k.val ((l.get p.1).val * (l.get p.2).val))).card

noncomputable def numBadPairs (l : List Std.I64) (k : Std.I64) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin l.length × Fin l.length =>
    p.1 < p.2 ∧ ¬ DivisibleBy k.val ((l.get p.1).val * (l.get p.2).val))).card

noncomputable def numGoodOrderedPairs (l : List Std.I64) (k : Std.I64) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : Fin l.length × Fin l.length =>
    p.1 ≠ p.2 ∧ DivisibleBy k.val ((l.get p.1).val * (l.get p.2).val))).card

/-- The function returns a result r, and r is the number of pairs (i, j) such that 0 <= i < j < n and k divides nums[i] * nums[j]. Here k divides an integer m means there exists an integer q with m = q * k.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = (numGoodPairs nums.val k : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = (numGoodPairs nums.val k : ℤ)) := by
  sorry

/-- The function does not fail on these inputs: it returns a result rather than overflowing, accessing out of bounds, or panicking.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∃ r : Std.I64, count_pairs nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∃ r : Std.I64, count_pairs nums k = ok r) := by
  sorry

/-- If the function returns r, then 0 <= r <= n*(n - 1)/2.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∀ r : Std.I64, count_pairs nums k = ok r →
      0 ≤ r.val ∧ r.val ≤ (totalPairs nums.val.length : ℤ)) := by
  sorry

/-- The function returns r = 1 if k divides nums[0] * nums[1], and returns r = 0 otherwise.
  Preconditions: Let n = len(nums). We have n = 2, 1 <= k <= 100000, and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 2)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    (DivisibleBy k.val
        ((nums.val.get ⟨0, by omega⟩).val * (nums.val.get ⟨1, by omega⟩).val) →
      count_pairs nums k = ok 1#i64) ∧
    (¬ DivisibleBy k.val
        ((nums.val.get ⟨0, by omega⟩).val * (nums.val.get ⟨1, by omega⟩).val) →
      count_pairs nums k = ok 0#i64) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn : nums.val.length = 2)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), (DivisibleBy k.val
        ((nums.val.get ⟨0, by omega⟩).val * (nums.val.get ⟨1, by omega⟩).val) →
      count_pairs nums k = ok 1#i64) ∧
    (¬ DivisibleBy k.val
        ((nums.val.get ⟨0, by omega⟩).val * (nums.val.get ⟨1, by omega⟩).val) →
      count_pairs nums k = ok 0#i64)) := by
  sorry

/-- The function returns r = n*(n - 1)/2.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; and k divides nums[i] for every i with 0 <= i < n. -/
theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hdiv : ∀ i : Fin nums.val.length, DivisibleBy k.val (nums.val.get i).val) :
    ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = (totalPairs nums.val.length : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hdiv : ∀ i : Fin nums.val.length, DivisibleBy k.val (nums.val.get i).val), ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = (totalPairs nums.val.length : ℤ)) := by
  sorry

/-- Let M be the number of pairs (i, j) with 0 <= i < j < n such that k does not divide nums[i] * nums[j]. If the function returns r, then r + M = n*(n - 1)/2.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums k = ok r →
      r.val + (numBadPairs nums.val k : ℤ) = (totalPairs nums.val.length : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∀ r : Std.I64, count_pairs nums k = ok r →
      r.val + (numBadPairs nums.val k : ℤ) = (totalPairs nums.val.length : ℤ)) := by
  sorry

/-- Let O be the number of ordered pairs (i, j) with 0 <= i < n, 0 <= j < n, i != j, and k divides nums[i] * nums[j]. If the function returns r, then 2*r = O.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums k = ok r →
      2 * r.val = (numGoodOrderedPairs nums.val k : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∀ r : Std.I64, count_pairs nums k = ok r →
      2 * r.val = (numGoodOrderedPairs nums.val k : ℤ)) := by
  sorry

/-- The calls count_pairs nums k and count_pairs nums' k both return results r and r', and r = r'.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. Let nums' be any slice of length n that is a permutation of nums (the same multiset of entries). -/
theorem spec_8 (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : nums'.val.Perm nums.val) :
    ∃ r r' : Std.I64,
      count_pairs nums k = ok r ∧ count_pairs nums' k = ok r' ∧ r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hlen : nums'.val.length = nums.val.length)
    (hperm : nums'.val.Perm nums.val), ∃ r r' : Std.I64,
      count_pairs nums k = ok r ∧ count_pairs nums' k = ok r' ∧ r.val = r'.val) := by
  sorry

/-- If count_pairs nums k1 returns r1 and count_pairs nums k2 returns r2, then r2 <= r1.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; for every i with 0 <= i < n, 1 <= nums[i] <= 100000; and 1 <= k1 <= 100000, 1 <= k2 <= 100000 with k1 dividing k2. -/
theorem spec_9 (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hk1a : 1 ≤ k1.val) (hk1b : k1.val ≤ 100000)
    (hk2a : 1 ≤ k2.val) (hk2b : k2.val ≤ 100000)
    (hdvd : DivisibleBy k1.val k2.val) :
    ∀ r1 : Std.I64, count_pairs nums k1 = ok r1 →
      ∀ r2 : Std.I64, count_pairs nums k2 = ok r2 → r2.val ≤ r1.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000)
    (hk1a : 1 ≤ k1.val) (hk1b : k1.val ≤ 100000)
    (hk2a : 1 ≤ k2.val) (hk2b : k2.val ≤ 100000)
    (hdvd : DivisibleBy k1.val k2.val), ∀ r1 : Std.I64, count_pairs nums k1 = ok r1 →
      ∀ r2 : Std.I64, count_pairs nums k2 = ok r2 → r2.val ≤ r1.val) := by
  sorry

/-- If the function returns r, then r > 0 if and only if there exists a pair (i, j) with 0 <= i < j < n such that k divides nums[i] * nums[j].
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and for every i with 0 <= i < n, 1 <= nums[i] <= 100000. -/
theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000) :
    ∀ r : Std.I64, count_pairs nums k = ok r →
      (0 < r.val ↔ ∃ (i j : Fin nums.val.length), i < j ∧
        DivisibleBy k.val ((nums.val.get i).val * (nums.val.get j).val)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hval : ∀ i : Fin nums.val.length,
      1 ≤ (nums.val.get i).val ∧ (nums.val.get i).val ≤ 100000), ∀ r : Std.I64, count_pairs nums k = ok r →
      (0 < r.val ↔ ∃ (i j : Fin nums.val.length), i < j ∧
        DivisibleBy k.val ((nums.val.get i).val * (nums.val.get j).val))) := by
  sorry

/-- The function returns r = n*(n - 1)/2 if k divides x*x, and returns r = 0 otherwise.
  Preconditions: Let n = len(nums). We have 1 <= n <= 100000; 1 <= k <= 100000; and there exists x with 1 <= x <= 100000 such that nums[i] = x for every i with 0 <= i < n. -/
theorem spec_11 (nums : Slice Std.I64) (k : Std.I64) (x : ℤ)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 100000)
    (hconst : ∀ i : Fin nums.val.length, (nums.val.get i).val = x) :
    (DivisibleBy k.val (x * x) →
      ∃ r : Std.I64, count_pairs nums k = ok r ∧
        r.val = (totalPairs nums.val.length : ℤ)) ∧
    (¬ DivisibleBy k.val (x * x) →
      ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = 0) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (x : ℤ)
    (hn1 : 1 ≤ nums.val.length) (hn2 : nums.val.length ≤ 100000)
    (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 100000)
    (hx1 : 1 ≤ x) (hx2 : x ≤ 100000)
    (hconst : ∀ i : Fin nums.val.length, (nums.val.get i).val = x), (DivisibleBy k.val (x * x) →
      ∃ r : Std.I64, count_pairs nums k = ok r ∧
        r.val = (totalPairs nums.val.length : ℤ)) ∧
    (¬ DivisibleBy k.val (x * x) →
      ∃ r : Std.I64, count_pairs nums k = ok r ∧ r.val = 0)) := by
  sorry

end AegisSpec.CountPairs
