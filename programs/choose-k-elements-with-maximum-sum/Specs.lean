import Aegis.FindMaxSum.Code.Funs

/-!
# Specifications of `Aegis.FindMaxSum.find_max_sum`

LeetCode problem `choose-k-elements-with-maximum-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.FindMaxSum

def ival (nums : List Std.I64) (i : ℕ) : ℤ := (nums.getD i default).val

def smallerIdx (nums1 : List Std.I64) (n i : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun j => ival nums1 j < ival nums1 i)

def sumOver (nums2 : List Std.I64) (T : Finset ℕ) : ℤ := ∑ j ∈ T, ival nums2 j

noncomputable def bestSum (nums2 : List Std.I64) (S : Finset ℕ) (k : ℤ) : ℤ := by
  classical
  exact
    if h : (S.powerset.filter (fun T => (T.card : ℤ) ≤ k)).Nonempty then
      (S.powerset.filter (fun T => (T.card : ℤ) ≤ k)).sup' h (fun T => sumOver nums2 T)
    else 0

noncomputable def maxOver (nums : List Std.I64) (n : ℕ) : ℤ := by
  classical
  exact if h : (Finset.range n).Nonempty then (Finset.range n).sup' h (ival nums) else 0

noncomputable def minOver (nums : List Std.I64) (S : Finset ℕ) : ℤ := by
  classical
  exact if h : S.Nonempty then S.inf' h (ival nums) else 0

/-- The function returns a result r and for every i with 0 ≤ i < n, r[i] = max { Σ_{j∈T} nums2[j] | T ⊆ S_i and |T| ≤ k }, where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] } and the maximum is over all subsets T of S_i with at most k elements (the empty set is allowed and contributes 0).
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_1 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∃ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r ∧
      ∀ i, i < n →
        ival r.val i = bestSum nums2.val (smallerIdx nums1.val n i) k.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∃ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r ∧
      ∀ i, i < n →
        ival r.val i = bestSum nums2.val (smallerIdx nums1.val n i) k.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n, where n = len(nums1).
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_2 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r → r.val.length = n := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r → r.val.length = n) := by
  sorry

/-- The function returns a result r (it does not fail).
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_3 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∃ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∃ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, 0 ≤ r[i] ≤ k * max_{0≤j<n} nums2[j].
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_4 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → 0 ≤ ival r.val i ∧ ival r.val i ≤ k.val * maxOver nums2.val n := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → 0 ≤ ival r.val i ∧ ival r.val i ≤ k.val * maxOver nums2.val n) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, if |S_i| ≤ k (as integers), then r[i] = Σ_{j∈S_i} nums2[j], where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] }.
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_5 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ((smallerIdx nums1.val n i).card : ℤ) ≤ k.val →
        ival r.val i = sumOver nums2.val (smallerIdx nums1.val n i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ((smallerIdx nums1.val n i).card : ℤ) ≤ k.val →
        ival r.val i = sumOver nums2.val (smallerIdx nums1.val n i)) := by
  sorry

/-- Whenever the function returns a result r, for every i and i' with 0 ≤ i < n and 0 ≤ i' < n, if nums1[i] = nums1[i'], then r[i] = r[i'].
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_6 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i i' : ℕ, i < n → i' < n → ival nums1.val i = ival nums1.val i' →
        ival r.val i = ival r.val i' := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i i' : ℕ, i < n → i' < n → ival nums1.val i = ival nums1.val i' →
        ival r.val i = ival r.val i') := by
  sorry

/-- Whenever the function returns a result r, for every i and i' with 0 ≤ i < n and 0 ≤ i' < n, if nums1[i] < nums1[i'], then r[i] ≤ r[i'].
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_7 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i i' : ℕ, i < n → i' < n → ival nums1.val i < ival nums1.val i' →
        ival r.val i ≤ ival r.val i' := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i i' : ℕ, i < n → i' < n → ival nums1.val i < ival nums1.val i' →
        ival r.val i ≤ ival r.val i') := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, r[i] = 0 if and only if S_i is empty, where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] }.
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_8 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → (ival r.val i = 0 ↔ smallerIdx nums1.val n i = ∅) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → (ival r.val i = 0 ↔ smallerIdx nums1.val n i = ∅)) := by
  sorry

/-- Let r1 be the result of find_max_sum(nums1, nums2, k1) and r2 be the result of find_max_sum(nums1, nums2, k2). If both calls return results r1 and r2, then for every i with 0 ≤ i < n, r1[i] ≤ r2[i].
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000. For the two invocations considered, let k1 and k2 be integers with 1 ≤ k1 ≤ k2 ≤ n. -/
theorem spec_9 (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk1 : 1 ≤ k1.val ∧ k1.val ≤ (n : ℤ))
    (hk2 : 1 ≤ k2.val ∧ k2.val ≤ (n : ℤ))
    (hk12 : k1.val ≤ k2.val) :
    ∀ r1 r2,
      Aegis.FindMaxSum.find_max_sum nums1 nums2 k1 = ok r1 →
      Aegis.FindMaxSum.find_max_sum nums1 nums2 k2 = ok r2 →
        ∀ i, i < n → ival r1.val i ≤ ival r2.val i := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k1 k2 : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk1 : 1 ≤ k1.val ∧ k1.val ≤ (n : ℤ))
    (hk2 : 1 ≤ k2.val ∧ k2.val ≤ (n : ℤ))
    (hk12 : k1.val ≤ k2.val), ∀ r1 r2,
      Aegis.FindMaxSum.find_max_sum nums1 nums2 k1 = ok r1 →
      Aegis.FindMaxSum.find_max_sum nums1 nums2 k2 = ok r2 →
        ∀ i, i < n → ival r1.val i ≤ ival r2.val i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, r[i] ≤ Σ_{j∈S_i} nums2[j], where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] }.
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_10 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ival r.val i ≤ sumOver nums2.val (smallerIdx nums1.val n i) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ival r.val i ≤ sumOver nums2.val (smallerIdx nums1.val n i)) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, if S_i is nonempty, then r[i] ≥ min(k, |S_i|) * min_{j∈S_i} nums2[j], where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] } and min(k, |S_i|) is the integer minimum.
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_11 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → (smallerIdx nums1.val n i).Nonempty →
        min k.val ((smallerIdx nums1.val n i).card : ℤ) *
            minOver nums2.val (smallerIdx nums1.val n i) ≤ ival r.val i := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → (smallerIdx nums1.val n i).Nonempty →
        min k.val ((smallerIdx nums1.val n i).card : ℤ) *
            minOver nums2.val (smallerIdx nums1.val n i) ≤ ival r.val i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 ≤ i < n, there exists a subset T_i ⊆ S_i such that |T_i| = min(k, |S_i|) (as integers), r[i] = Σ_{j∈T_i} nums2[j], and for every j ∈ T_i and every j' ∈ S_i \ T_i, nums2[j] ≥ nums2[j'], where S_i = { j | 0 ≤ j < n and nums1[j] < nums1[i] }.
  Preconditions: Let n = len(nums1). Then len(nums2) = n, 1 ≤ n ≤ 100000, for every i with 0 ≤ i < n we have 1 ≤ nums1[i] ≤ 1000000 and 1 ≤ nums2[i] ≤ 1000000, and 1 ≤ k ≤ n (as integers). -/
theorem spec_12 (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)) :
    ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ∃ T : Finset ℕ,
        T ⊆ smallerIdx nums1.val n i ∧
        (T.card : ℤ) = min k.val ((smallerIdx nums1.val n i).card : ℤ) ∧
        ival r.val i = sumOver nums2.val T ∧
        ∀ j ∈ T, ∀ j' ∈ smallerIdx nums1.val n i, j' ∉ T →
          ival nums2.val j ≥ ival nums2.val j' := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn1 : nums1.val.length = n) (hn2 : nums2.val.length = n)
    (hn_pos : 1 ≤ n) (hn_le : n ≤ 100000)
    (hb1 : ∀ i, i < n → 1 ≤ ival nums1.val i ∧ ival nums1.val i ≤ 1000000)
    (hb2 : ∀ i, i < n → 1 ≤ ival nums2.val i ∧ ival nums2.val i ≤ 1000000)
    (hk : 1 ≤ k.val ∧ k.val ≤ (n : ℤ)), ∀ r, Aegis.FindMaxSum.find_max_sum nums1 nums2 k = ok r →
      ∀ i, i < n → ∃ T : Finset ℕ,
        T ⊆ smallerIdx nums1.val n i ∧
        (T.card : ℤ) = min k.val ((smallerIdx nums1.val n i).card : ℤ) ∧
        ival r.val i = sumOver nums2.val T ∧
        ∀ j ∈ T, ∀ j' ∈ smallerIdx nums1.val n i, j' ∉ T →
          ival nums2.val j ≥ ival nums2.val j') := by
  sorry

end AegisSpec.FindMaxSum
