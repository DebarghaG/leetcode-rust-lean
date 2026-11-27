import Aegis.FindNumberOfLis.Code.Funs

/-!
# Specifications of `Aegis.FindNumberOfLis.find_number_of_lis`

LeetCode problem `number-of-longest-increasing-subsequence`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindNumberOfLis

def vals (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

def valAt (v : List ℤ) (i : ℕ) : ℤ := v.getD i 0

def IsIncIndexSet (v : List ℤ) (s : Finset ℕ) : Prop :=
  s ⊆ Finset.range v.length ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → valAt v i < valAt v j

noncomputable def lisLen (v : List ℤ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter (IsIncIndexSet v)).sup Finset.card

noncomputable def lisCount (v : List ℤ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter
    (fun s => IsIncIndexSet v s ∧ s.card = lisLen v)).card

def IsNonIncreasing (v : List ℤ) : Prop :=
  ∀ i j, i < j → j < v.length → valAt v j ≤ valAt v i

def IsNonDecreasing (v : List ℤ) : Prop :=
  ∀ i j, i < j → j < v.length → valAt v i ≤ valAt v j

noncomputable def occCount (v : List ℤ) (x : ℤ) : ℕ :=
  ((Finset.range v.length).filter (fun i => valAt v i = x)).card

noncomputable def multiplicityProduct (v : List ℤ) : ℕ :=
  v.toFinset.prod (occCount v)

noncomputable def pairCount (v : List ℤ) (a b : ℤ) : ℕ :=
  ((Finset.range v.length).filter (fun i => valAt v i = a)).sum
    (fun i => ((Finset.range v.length).filter (fun j => i < j ∧ valAt v j = b)).card)

def IsIncIndexSetEndingAt (v : List ℤ) (i : ℕ) (s : Finset ℕ) : Prop :=
  IsIncIndexSet v s ∧ i ∈ s ∧ ∀ j ∈ s, j ≤ i

noncomputable def endLen (v : List ℤ) (i : ℕ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter (IsIncIndexSetEndingAt v i)).sup Finset.card

noncomputable def endCount (v : List ℤ) (i : ℕ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter
    (fun s => IsIncIndexSetEndingAt v i s ∧ s.card = endLen v i)).card

noncomputable def maxEndLen (v : List ℤ) : ℕ :=
  (Finset.range v.length).sup (endLen v)

noncomputable def predIdx (v : List ℤ) (i : ℕ) : Finset ℕ :=
  (Finset.range i).filter (fun j => j < v.length ∧ valAt v j < valAt v i)

noncomputable def predMaxLen (v : List ℤ) (i : ℕ) : ℕ := (predIdx v i).sup (endLen v)

noncomputable def predCountSum (v : List ℤ) (i : ℕ) : ℕ :=
  ((predIdx v i).filter (fun j => endLen v j + 1 = endLen v i)).sum (endCount v)

def dagEdge (v : List ℤ) (i j : ℕ) : Prop :=
  i < j ∧ j < v.length ∧ valAt v i < valAt v j

def IsDagPath (v : List ℤ) (p : List ℕ) : Prop :=
  p ≠ [] ∧ (∀ i ∈ p, i < v.length) ∧ p.Pairwise (dagEdge v)

def IsDagPathSet (v : List ℤ) (s : Finset ℕ) : Prop :=
  s ⊆ Finset.range v.length ∧ s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → dagEdge v i j

noncomputable def maxPathLen (v : List ℤ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter (IsDagPathSet v)).sup Finset.card

noncomputable def maxPathCount (v : List ℤ) : ℕ := by
  classical
  exact ((Finset.range v.length).powerset.filter
    (fun s => IsDagPathSet v s ∧ s.card = maxPathLen v)).card

/-- Whenever the function returns a result r, r equals the number of longest increasing subsequences of nums. An increasing subsequence of nums is a sequence of indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_0 and i_{k-1} < len(nums) such that nums[i_0] < nums[i_1] < ... < nums[i_{k-1}]. A longest increasing subsequence (LIS) is an increasing subsequence of maximum length. The answer is the number of such index sequences of maximum length.
  Preconditions: The input nums is a slice of i64 satisfying: 1 <= len(nums) <= 2000; for every i with 0 <= i < len(nums), -10^6 <= nums[i] <= 10^6; and the number of longest increasing subsequences of nums is at most 2147483647. -/
theorem spec_1 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (lisCount (vals nums) : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (lisCount (vals nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r >= 1.
  Preconditions: Same as spec_1. -/
theorem spec_2 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r → 1 ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r → 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r = len(nums).
  Preconditions: Same as spec_1, and additionally for all i, j with 0 <= i < j < len(nums), nums[i] >= nums[j] (i.e., nums is non-increasing). -/
theorem spec_3 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hmono : IsNonIncreasing (vals nums)) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (nums.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hmono : IsNonIncreasing (vals nums)), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (nums.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, r = the product, over all distinct values v that appear in nums, of the number of times v appears in nums.
  Preconditions: Same as spec_1, and additionally for all i, j with 0 <= i < j < len(nums), nums[i] <= nums[j] (i.e., nums is non-decreasing). -/
theorem spec_4 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hmono : IsNonDecreasing (vals nums)) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (multiplicityProduct (vals nums) : ℤ) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hmono : IsNonDecreasing (vals nums)), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (multiplicityProduct (vals nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r on nums and a result r' on nums', r = r'.
  Preconditions: Same as spec_1. Let nums' be any slice of i64 of the same length as nums such that for all i, j with 0 <= i, j < len(nums), nums[i] < nums[j] iff nums'[i] < nums'[j] and nums[i] = nums[j] iff nums'[i] = nums'[j]. Assume nums' also satisfies the input constraints: 1 <= len(nums') <= 2000 and for every i, -10^6 <= nums'[i] <= 10^6, and the number of LIS of nums' fits in 32-bit. -/
theorem spec_5 (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 2000)
    (hval' : ∀ x ∈ nums'.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount' : lisCount (vals nums') ≤ 2147483647)
    (hlen : nums'.val.length = nums.val.length)
    (hlt : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valAt (vals nums) i < valAt (vals nums) j ↔
        valAt (vals nums') i < valAt (vals nums') j))
    (heq : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valAt (vals nums) i = valAt (vals nums) j ↔
        valAt (vals nums') i = valAt (vals nums') j)) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      Aegis.FindNumberOfLis.find_number_of_lis nums' = ok r' → r = r' := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums nums' : Slice Std.I64) (r r' : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (hlen_pos' : 1 ≤ nums'.val.length) (hlen_le' : nums'.val.length ≤ 2000)
    (hval' : ∀ x ∈ nums'.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount' : lisCount (vals nums') ≤ 2147483647)
    (hlen : nums'.val.length = nums.val.length)
    (hlt : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valAt (vals nums) i < valAt (vals nums) j ↔
        valAt (vals nums') i < valAt (vals nums') j))
    (heq : ∀ i j, i < nums.val.length → j < nums.val.length →
      (valAt (vals nums) i = valAt (vals nums) j ↔
        valAt (vals nums') i = valAt (vals nums') j)), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      Aegis.FindNumberOfLis.find_number_of_lis nums' = ok r' → r = r') := by
  sorry

/-- Whenever the function returns a result r, r equals the number of paths of maximum length in the directed acyclic graph G with vertex set {0, 1, ..., len(nums)-1} and a directed edge from i to j if and only if i < j and nums[i] < nums[j]. A path is a sequence of vertices v_0, v_1, ..., v_{k-1} with an edge from v_t to v_{t+1} for each 0 <= t < k-1. The length of a path is the number of vertices k. The answer is the number of paths of maximum length.
  Preconditions: Same as spec_1. -/
theorem spec_6 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (maxPathCount (vals nums) : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = (maxPathCount (vals nums) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let L_i be the maximum length of an increasing subsequence of nums ending at index i (i.e., whose last index is i), and let C_i be the number of such subsequences of length L_i, for each i with 0 <= i < len(nums). Let L = max_{0 <= i < len(nums)} L_i. Then r = sum_{i: L_i = L} C_i.
  Preconditions: Same as spec_1. -/
theorem spec_7 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = ((((Finset.range nums.val.length).filter
        (fun i => endLen (vals nums) i = maxEndLen (vals nums))).sum
        (endCount (vals nums)) : ℕ) : ℤ) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val = ((((Finset.range nums.val.length).filter
        (fun i => endLen (vals nums) i = maxEndLen (vals nums))).sum
        (endCount (vals nums)) : ℕ) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, let L be the maximum length of an increasing subsequence of nums. Then r <= C(len(nums), L), where C(n, L) is the binomial coefficient (the number of subsets of {0, ..., n-1} of size L).
  Preconditions: Same as spec_1. -/
theorem spec_8 (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val ≤ (Nat.choose nums.val.length (lisLen (vals nums)) : ℤ) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      r.val ≤ (Nat.choose nums.val.length (lisLen (vals nums)) : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if there exists a pair of indices i, j with 0 <= i < j < len(nums), nums[i] = a, and nums[j] = b, then r equals the number of such pairs (i, j). Otherwise (i.e., there is no such pair), r = len(nums).
  Preconditions: Same as spec_1, and additionally nums contains exactly two distinct values. Let a and b be these two values with a < b. -/
theorem spec_9 (nums : Slice Std.I64) (r : Std.I64) (a b : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (ha : a ∈ (vals nums).toFinset) (hb : b ∈ (vals nums).toFinset) (hab : a < b)
    (hexactly : ∀ x ∈ (vals nums).toFinset, x = a ∨ x = b) :
    Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      ((∃ i j, i < j ∧ j < nums.val.length ∧
          valAt (vals nums) i = a ∧ valAt (vals nums) j = b) →
        r.val = (pairCount (vals nums) a b : ℤ)) ∧
      (¬ (∃ i j, i < j ∧ j < nums.val.length ∧
          valAt (vals nums) i = a ∧ valAt (vals nums) j = b) →
        r.val = (nums.val.length : ℤ)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (r : Std.I64) (a b : ℤ)
    (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 2000)
    (hval : ∀ x ∈ nums.val, -1000000 ≤ x.val ∧ x.val ≤ 1000000)
    (hcount : lisCount (vals nums) ≤ 2147483647)
    (ha : a ∈ (vals nums).toFinset) (hb : b ∈ (vals nums).toFinset) (hab : a < b)
    (hexactly : ∀ x ∈ (vals nums).toFinset, x = a ∨ x = b), Aegis.FindNumberOfLis.find_number_of_lis nums = ok r →
      ((∃ i j, i < j ∧ j < nums.val.length ∧
          valAt (vals nums) i = a ∧ valAt (vals nums) j = b) →
        r.val = (pairCount (vals nums) a b : ℤ)) ∧
      (¬ (∃ i j, i < j ∧ j < nums.val.length ∧
          valAt (vals nums) i = a ∧ valAt (vals nums) j = b) →
        r.val = (nums.val.length : ℤ))) := by
  sorry

end AegisSpec.FindNumberOfLis
