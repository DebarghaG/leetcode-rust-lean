import Aegis.MaxNumOfMarkedIndices.Code.Funs

/-!
# Specifications of `Aegis.MaxNumOfMarkedIndices.max_num_of_marked_indices`

LeetCode problem `find-the-maximum-number-of-marked-indices`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxNumOfMarkedIndices (max_num_of_marked_indices)

namespace AegisSpec.MaxNumOfMarkedIndices

def vals (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def LenOk (nums : Slice I64) : Prop :=
  1 ≤ nums.val.length ∧ nums.val.length ≤ 100000

def ValOk (nums : Slice I64) : Prop :=
  ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 10 ^ 9

def Pre (nums : Slice I64) : Prop := LenOk nums ∧ ValOk nums

def PairGood (nums : Slice I64) (p : Nat × Nat) : Prop :=
  ∃ vi vj : I64, nums.val[p.1]? = some vi ∧ nums.val[p.2]? = some vj ∧ 2 * vi.val ≤ vj.val

def IsMarking (nums : Slice I64) (pairs : List (Nat × Nat)) : Prop :=
  (pairs.map Prod.fst ++ pairs.map Prod.snd).Nodup ∧ ∀ p ∈ pairs, PairGood nums p

def HasMarkingOfSize (nums : Slice I64) (k : Nat) : Prop :=
  ∃ pairs : List (Nat × Nat), IsMarking nums pairs ∧ pairs.length = k

def IsMaxMarking (nums : Slice I64) (k : Nat) : Prop :=
  HasMarkingOfSize nums k ∧ ∀ k' : Nat, HasMarkingOfSize nums k' → k' ≤ k

def sortedVals (nums : Slice I64) : List Int :=
  (vals nums).mergeSort (fun a b => decide (a ≤ b))

def nth (a : List Int) (i : Nat) : Int := a.getD i 0

def Feasible (a : List Int) (k : Nat) : Prop :=
  k ≤ a.length / 2 ∧ ∀ i : Nat, i < k → 2 * nth a i ≤ nth a (a.length - k + i)

def IsMaxFeasible (a : List Int) (k : Nat) : Prop :=
  Feasible a k ∧ ∀ k' : Nat, Feasible a k' → k' ≤ k

def minVal (nums : Slice I64) : Int := (vals nums).min?.getD 0

def maxVal (nums : Slice I64) : Int := (vals nums).max?.getD 0

def IsScaledBy (c : Int) (nums nums' : Slice I64) : Prop :=
  nums'.val.length = nums.val.length ∧ vals nums' = (vals nums).map (fun v => c * v)

def IsPermOf (nums1 nums2 : Slice I64) : Prop := (vals nums2).Perm (vals nums1)

/-- The function returns a result r and r = 2 * k, where k is the maximum cardinality of a set of pairs of indices (i_1, j_1), ..., (i_k, j_k) such that: (1) all 2k indices are pairwise distinct and lie in the range 0 <= index < len(nums); (2) for each p from 1 to k, 2 * nums[i_p] <= nums[j_p].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_1 (nums : Slice I64) (hpre : Pre nums) :
    ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      ∃ k : Nat, IsMaxMarking nums k ∧ r.val = 2 * (k : Int) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      ∃ k : Nat, IsMaxMarking nums k ∧ r.val = 2 * (k : Int)) := by
  sorry

/-- The function returns a result r (it does not fail, panic, or overflow).
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_2 (nums : Slice I64) (hpre : Pre nums) :
    ∃ r : I64, max_num_of_marked_indices nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∃ r : I64, max_num_of_marked_indices nums = ok r) := by
  sorry

/-- Let n = len(nums). Let a_0 <= a_1 <= ... <= a_{n-1} be the elements of nums sorted in non-decreasing order. The function returns a result r and r = 2 * k_max, where k_max is the largest integer k with 0 <= k <= n / 2 (integer division) such that for every i with 0 <= i < k, 2 * a_i <= a_{n-k+i}.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_3 (nums : Slice I64) (hpre : Pre nums) :
    ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      ∃ k : Nat, IsMaxFeasible (sortedVals nums) k ∧ r.val = 2 * (k : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      ∃ k : Nat, IsMaxFeasible (sortedVals nums) k ∧ r.val = 2 * (k : Int)) := by
  sorry

/-- Whenever the function returns a result r, r is an even integer and 0 <= r <= len(nums).
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_4 (nums : Slice I64) (hpre : Pre nums) :
    ∀ r : I64, max_num_of_marked_indices nums = ok r →
      (∃ m : Int, r.val = 2 * m) ∧ 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∀ r : I64, max_num_of_marked_indices nums = ok r →
      (∃ m : Int, r.val = 2 * m) ∧ 0 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
  sorry

/-- The function returns a result r and r = 0 if and only if there do not exist two distinct indices i and j with 0 <= i, j < len(nums) and 2 * nums[i] <= nums[j].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_5 (nums : Slice I64) (hpre : Pre nums) :
    ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      (r.val = 0 ↔ ¬ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧ PairGood nums (i, j)) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      (r.val = 0 ↔ ¬ ∃ i j : Nat,
        i < nums.val.length ∧ j < nums.val.length ∧ i ≠ j ∧ PairGood nums (i, j))) := by
  sorry

/-- The function returns a result r and r = 0 if and only if 2 * min(nums) > max(nums), where min(nums) and max(nums) are the minimum and maximum values among the elements of nums.
  Preconditions: 1 <= len(nums) <= 100000, len(nums) >= 2, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_6 (nums : Slice I64) (hpre : Pre nums) (hlen : 2 ≤ nums.val.length) :
    ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      (r.val = 0 ↔ 2 * minVal nums > maxVal nums) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums) (hlen : 2 ≤ nums.val.length), ∃ r : I64, max_num_of_marked_indices nums = ok r ∧
      (r.val = 0 ↔ 2 * minVal nums > maxVal nums)) := by
  sorry

/-- Whenever the function returns a result r, there exists an integer m >= 0 with r = 2m and a set of m disjoint pairs of distinct indices (i_1, j_1), ..., (i_m, j_m) such that for each p from 1 to m, 0 <= i_p, j_p < len(nums), all 2m indices are pairwise distinct, and 2 * nums[i_p] <= nums[j_p].
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_7 (nums : Slice I64) (hpre : Pre nums) :
    ∀ r : I64, max_num_of_marked_indices nums = ok r →
      ∃ (m : Nat) (pairs : List (Nat × Nat)),
        IsMarking nums pairs ∧ pairs.length = m ∧ r.val = 2 * (m : Int) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∀ r : I64, max_num_of_marked_indices nums = ok r →
      ∃ (m : Nat) (pairs : List (Nat × Nat)),
        IsMarking nums pairs ∧ pairs.length = m ∧ r.val = 2 * (m : Int)) := by
  sorry

/-- Whenever the function returns a result r, for any integer m >= 0 and any set of m disjoint pairs of distinct indices (i_1, j_1), ..., (i_m, j_m) satisfying 0 <= i_p, j_p < len(nums), all 2m indices pairwise distinct, and 2 * nums[i_p] <= nums[j_p] for all p, we have 2 * m <= r.
  Preconditions: 1 <= len(nums) <= 100000, and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. -/
theorem spec_8 (nums : Slice I64) (hpre : Pre nums) :
    ∀ r : I64, max_num_of_marked_indices nums = ok r →
      ∀ pairs : List (Nat × Nat), IsMarking nums pairs → 2 * (pairs.length : Int) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (hpre : Pre nums), ∀ r : I64, max_num_of_marked_indices nums = ok r →
      ∀ pairs : List (Nat × Nat), IsMarking nums pairs → 2 * (pairs.length : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns r on nums and r' on nums', we have r = r'.
  Preconditions: 1 <= len(nums) <= 100000, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9. Let c be a positive integer such that for every i, 1 <= c * nums[i] <= 10^9. Let nums' be the slice of length len(nums) defined by nums'[i] = c * nums[i]. -/
theorem spec_9 (nums nums' : Slice I64) (c : Int) (hpre : Pre nums) (hc : 0 < c)
    (hbounds : ∀ v ∈ vals nums, 1 ≤ c * v ∧ c * v ≤ 10 ^ 9)
    (hscale : IsScaledBy c nums nums') :
    ∀ r r' : I64, max_num_of_marked_indices nums = ok r →
      max_num_of_marked_indices nums' = ok r' → r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice I64) (c : Int) (hpre : Pre nums) (hc : 0 < c)
    (hbounds : ∀ v ∈ vals nums, 1 ≤ c * v ∧ c * v ≤ 10 ^ 9)
    (hscale : IsScaledBy c nums nums'), ∀ r r' : I64, max_num_of_marked_indices nums = ok r →
      max_num_of_marked_indices nums' = ok r' → r.val = r'.val) := by
  sorry

/-- Whenever the function returns r1 on nums1 and r2 on nums2, we have r1 = r2.
  Preconditions: nums1 and nums2 are slices of the same length n with 1 <= n <= 100000, for every i with 0 <= i < n, 1 <= nums1[i] <= 10^9, and nums2 is a permutation of nums1 (i.e., there exists a bijection π from {0,...,n-1} to itself such that nums2[i] = nums1[π(i)] for all i). -/
theorem spec_10 (nums1 nums2 : Slice I64) (hlen : nums1.val.length = nums2.val.length)
    (hpre : Pre nums1) (hperm : IsPermOf nums1 nums2) :
    ∀ r1 r2 : I64, max_num_of_marked_indices nums1 = ok r1 →
      max_num_of_marked_indices nums2 = ok r2 → r1.val = r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice I64) (hlen : nums1.val.length = nums2.val.length)
    (hpre : Pre nums1) (hperm : IsPermOf nums1 nums2), ∀ r1 r2 : I64, max_num_of_marked_indices nums1 = ok r1 →
      max_num_of_marked_indices nums2 = ok r2 → r1.val = r2.val) := by
  sorry

end AegisSpec.MaxNumOfMarkedIndices
