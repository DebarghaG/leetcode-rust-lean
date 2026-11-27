import Aegis.NumSubseq.Code.Funs

/-!
# Specifications of `Aegis.NumSubseq.num_subseq`

LeetCode problem `number-of-subsequences-that-satisfy-the-given-sum-condition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NumSubseq

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def IsValidSubset (nums : Slice Std.I64) (t : ℤ) (S : Finset (Fin (vals nums).length)) : Prop :=
  S.Nonempty ∧
    ∃ i ∈ S, ∃ j ∈ S,
      (∀ k ∈ S, (vals nums)[i] ≤ (vals nums)[k]) ∧
      (∀ k ∈ S, (vals nums)[k] ≤ (vals nums)[j]) ∧
      (vals nums)[i] + (vals nums)[j] ≤ t

noncomputable def count (nums : Slice Std.I64) (t : ℤ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin (vals nums).length)).powerset.filter
    (fun S => IsValidSubset nums t S)).card

def minVal (nums : Slice Std.I64) : ℤ := ((vals nums).min?).getD 0

def maxVal (nums : Slice Std.I64) : ℤ := ((vals nums).max?).getD 0

noncomputable def doubleCount (nums : Slice Std.I64) (t : ℤ) : ℕ := by
  classical
  exact ((vals nums).filter (fun x => 2 * x ≤ t)).length

def valAt (nums : Slice Std.I64) (i : ℕ) : ℤ := ((vals nums)[i]?).getD 0

def sortedVals (nums : Slice Std.I64) : List ℤ := (vals nums).mergeSort

def lastIdx (a : List ℤ) (t : ℤ) (i : ℕ) : Option ℕ :=
  (List.range a.length).foldl
    (fun acc j => if (a[i]?).getD 0 + (a[j]?).getD 0 ≤ t then some j else acc) none

def pairsSum (a : List ℤ) (t : ℤ) : ℤ :=
  ((List.range a.length).map (fun i =>
    match lastIdx a t i with
    | some j => if i ≤ j then (2 : ℤ) ^ (j - i) else 0
    | none => 0)).sum

/-- Let n = len(nums) and let C be the number of non-empty sets S subset of {0,...,n-1} such that min({nums[i] | i in S}) + max({nums[i] | i in S}) <= target. The function returns a result r, and r is the unique integer satisfying 0 <= r < 1000000007 and r is congruent to C modulo 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val (count nums target.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val (count nums target.val : ℤ)) := by
  sorry

/-- For every nums and target satisfying the preconditions, the function returns a result r; it does not fail, overflow, panic, or access out of bounds.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r) := by
  sorry

/-- Whenever the function returns a result r on inputs satisfying the preconditions, 0 <= r < 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000) :
    ∀ r, Aegis.NumSubseq.num_subseq nums target = ok r →
      0 ≤ r.val ∧ r.val < 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000), ∀ r, Aegis.NumSubseq.num_subseq nums target = ok r →
      0 ≤ r.val ∧ r.val < 1000000007) := by
  sorry

/-- Let n = len(nums). If target < 2 * min_{0<=i<n} nums[i], then the function returns r = 0.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_4 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hsmall : target.val < 2 * minVal nums) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧ r.val = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hsmall : target.val < 2 * minVal nums), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧ r.val = 0) := by
  sorry

/-- Let n = len(nums). If target >= 2 * max_{0<=i<n} nums[i], then the function returns r = (2^n - 1) modulo 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_5 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hbig : 2 * maxVal nums ≤ target.val) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      r.val = ((2 : ℤ) ^ (vals nums).length - 1) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hbig : 2 * maxVal nums ≤ target.val), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      r.val = ((2 : ℤ) ^ (vals nums).length - 1) % 1000000007) := by
  sorry

/-- Let n = len(nums) and let C be the exact number of non-empty index sets S subset of {0,...,n-1} with min({nums[i] | i in S}) + max({nums[i] | i in S}) <= target. If 2 * min_{0<=i<n} nums[i] <= target < 2 * max_{0<=i<n} nums[i] (which implies n >= 2), then 1 <= C <= 2^n - 2, and the function returns r with 0 <= r < 1000000007 and r congruent to C modulo 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlo : 2 * minVal nums ≤ target.val) (hhi : target.val < 2 * maxVal nums) :
    1 ≤ count nums target.val ∧
      count nums target.val ≤ 2 ^ (vals nums).length - 2 ∧
      ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        Int.ModEq 1000000007 r.val (count nums target.val : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlo : 2 * minVal nums ≤ target.val) (hhi : target.val < 2 * maxVal nums), 1 ≤ count nums target.val ∧
      count nums target.val ≤ 2 ^ (vals nums).length - 2 ∧
      ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        Int.ModEq 1000000007 r.val (count nums target.val : ℤ)) := by
  sorry

/-- If len(nums) = 2, let a = nums[0] and b = nums[1]. Then the function returns r = (I(2*a <= target) + I(2*b <= target) + I(a + b <= target)) modulo 1000000007, where I(P) is 1 when P is true and 0 otherwise.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlen_two : (vals nums).length = 2) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      r.val = ((if 2 * valAt nums 0 ≤ target.val then (1 : ℤ) else 0) +
               (if 2 * valAt nums 1 ≤ target.val then (1 : ℤ) else 0) +
               (if valAt nums 0 + valAt nums 1 ≤ target.val then (1 : ℤ) else 0))
              % 1000000007 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlen_two : (vals nums).length = 2), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      r.val = ((if 2 * valAt nums 0 ≤ target.val then (1 : ℤ) else 0) +
               (if 2 * valAt nums 1 ≤ target.val then (1 : ℤ) else 0) +
               (if valAt nums 0 + valAt nums 1 ≤ target.val then (1 : ℤ) else 0))
              % 1000000007) := by
  sorry

/-- For any two arrays nums and nums' of the same length, both satisfying the preconditions, that are permutations of each other (that is, contain the same multiset of values), and for the same target, the result returned on nums equals the result returned on nums'.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_8 (nums nums' : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hlen_ge' : 1 ≤ (vals nums').length) (hlen_le' : (vals nums').length ≤ 100000)
    (hrng' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlen_eq : (vals nums).length = (vals nums').length)
    (hperm : (vals nums).Perm (vals nums')) :
    ∀ r r', Aegis.NumSubseq.num_subseq nums target = ok r →
      Aegis.NumSubseq.num_subseq nums' target = ok r' → r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (hlen_ge' : 1 ≤ (vals nums').length) (hlen_le' : (vals nums').length ≤ 100000)
    (hrng' : ∀ x ∈ vals nums', 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000)
    (hlen_eq : (vals nums).length = (vals nums').length)
    (hperm : (vals nums).Perm (vals nums')), ∀ r r', Aegis.NumSubseq.num_subseq nums target = ok r →
      Aegis.NumSubseq.num_subseq nums' target = ok r' → r.val = r'.val) := by
  sorry

/-- Let n = len(nums), and let K be the number of indices i with 0 <= i < n and 2 * nums[i] <= target. Let C be the exact number of non-empty index sets S subset of {0,...,n-1} with min({nums[i] | i in S}) + max({nums[i] | i in S}) <= target. Then C >= K, and the function returns r with 0 <= r < 1000000007 and r congruent to C modulo 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_9 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000) :
    doubleCount nums target.val ≤ count nums target.val ∧
      ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        Int.ModEq 1000000007 r.val (count nums target.val : ℤ) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000), doubleCount nums target.val ≤ count nums target.val ∧
      ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
        0 ≤ r.val ∧ r.val < 1000000007 ∧
        Int.ModEq 1000000007 r.val (count nums target.val : ℤ)) := by
  sorry

/-- For any fixed nums satisfying the preconditions and any two targets t1 and t2 with 1 <= t1 <= t2 <= 1000000, let C1 and C2 be the exact numbers of valid non-empty subsequences for targets t1 and t2 respectively, defined as in the main specification. Then C1 <= C2. Moreover, if the function returns r1 on target t1 and r2 on target t2, then each of r1 and r2 is in [0, 1000000007) and is congruent, respectively, to spec_11 and C2 modulo 1000000007.
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000. -/
theorem spec_10 (nums : Slice Std.I64) (t1 t2 : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht1_ge : 1 ≤ t1.val) (ht_mono : t1.val ≤ t2.val) (ht2_le : t2.val ≤ 1000000) :
    count nums t1.val ≤ count nums t2.val ∧
      ∀ r1 r2, Aegis.NumSubseq.num_subseq nums t1 = ok r1 →
        Aegis.NumSubseq.num_subseq nums t2 = ok r2 →
        (0 ≤ r1.val ∧ r1.val < 1000000007 ∧
          Int.ModEq 1000000007 r1.val (count nums t1.val : ℤ)) ∧
        (0 ≤ r2.val ∧ r2.val < 1000000007 ∧
          Int.ModEq 1000000007 r2.val (count nums t2.val : ℤ)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (t1 t2 : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht1_ge : 1 ≤ t1.val) (ht_mono : t1.val ≤ t2.val) (ht2_le : t2.val ≤ 1000000), count nums t1.val ≤ count nums t2.val ∧
      ∀ r1 r2, Aegis.NumSubseq.num_subseq nums t1 = ok r1 →
        Aegis.NumSubseq.num_subseq nums t2 = ok r2 →
        (0 ≤ r1.val ∧ r1.val < 1000000007 ∧
          Int.ModEq 1000000007 r1.val (count nums t1.val : ℤ)) ∧
        (0 ≤ r2.val ∧ r2.val < 1000000007 ∧
          Int.ModEq 1000000007 r2.val (count nums t2.val : ℤ))) := by
  sorry

/-- Let n = len(nums), and let a be the nondecreasing permutation of nums, so a[0] <= ... <= a[n-1]. For each i with 0 <= i < n, let j(i) be the largest index j with 0 <= j < n and a[i] + a[j] <= target, or -1 if no such j exists. Then the function returns r with 0 <= r < 1000000007 and r congruent modulo 1000000007 to sum_{i=0}^{n-1} (if j(i) >= i then 2^{j(i)-i} else 0).
  Preconditions: len(nums) >= 1 and len(nums) <= 100000; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000; 1 <= target <= 1000000. -/
theorem spec_11 (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000) :
    ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val (pairsSum (sortedVals nums) target.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
    (hlen_ge : 1 ≤ (vals nums).length) (hlen_le : (vals nums).length ≤ 100000)
    (hrng : ∀ x ∈ vals nums, 1 ≤ x ∧ x ≤ 1000000)
    (ht_ge : 1 ≤ target.val) (ht_le : target.val ≤ 1000000), ∃ r, Aegis.NumSubseq.num_subseq nums target = ok r ∧
      0 ≤ r.val ∧ r.val < 1000000007 ∧
      Int.ModEq 1000000007 r.val (pairsSum (sortedVals nums) target.val)) := by
  sorry

end AegisSpec.NumSubseq
