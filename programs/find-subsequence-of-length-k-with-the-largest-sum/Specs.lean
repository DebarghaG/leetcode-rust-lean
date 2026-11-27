import Aegis.MaxSubsequence.Code.Funs

/-!
# Specifications of `Aegis.MaxSubsequence.max_subsequence`

LeetCode problem `find-subsequence-of-length-k-with-the-largest-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MaxSubsequence

def toInts (l : List Std.I64) : List Int := l.map (fun x => x.val)

def sumI (l : List Int) : Int := l.sum

def IsSubseq (s l : List Int) : Prop :=
  ∃ f : Fin s.length → Fin l.length, StrictMono f ∧ ∀ j, s.get j = l.get (f j)

def SortedDesc (l : List Int) : Prop := l.Pairwise (· ≥ ·)

def SortedAsc (l : List Int) : Prop := l.Pairwise (· ≤ ·)

def IsMax (M : Int) (l : List Int) : Prop := M ∈ l ∧ ∀ x ∈ l, x ≤ M

def IsDescOrdering (a l : List Int) : Prop := a.Perm l ∧ SortedDesc a

/-- The function returns a result r such that: (1) len(r) = k; (2) r is a subsequence of nums, i.e. there exist indices i_0 < i_1 < ... < i_{k-1} with 0 <= i_j < len(nums) and r[j] = nums[i_j] for every j with 0 <= j < k; and (3) Sum(r) is maximal among all length-k subsequences of nums: for every length-k subsequence s of nums, Sum(r) >= Sum(s), where Sum(x) = x[0] + ... + x[len(x)-1] as a mathematical integer. Equivalently, Sum(r) equals the maximum possible sum of a subsequence of nums of length k.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. Here k is interpreted as the natural number equal to its integer value, which is within the stated bounds. -/
theorem spec_1
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r ∧
      (r.val.length : Int) = k.val ∧
      IsSubseq (toInts r.val) (toInts nums.val) ∧
      (∀ s, IsSubseq s (toInts nums.val) → (s.length : Int) = k.val →
        sumI s ≤ sumI (toInts r.val)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r ∧
      (r.val.length : Int) = k.val ∧
      IsSubseq (toInts r.val) (toInts nums.val) ∧
      (∀ s, IsSubseq s (toInts nums.val) → (s.length : Int) = k.val →
        sumI s ≤ sumI (toInts r.val))) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r; it does not fail (no overflow, out-of-bounds access, panic, or other error).
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_2
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∃ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = k.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_3
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      (r.val.length : Int) = k.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      (r.val.length : Int) = k.val) := by
  sorry

/-- Whenever the function returns a result r, there exist integers i_0, i_1, ..., i_{k-1} such that 0 <= i_0 < i_1 < ... < i_{k-1} < len(nums) and, for every j with 0 <= j < k, r[j] = nums[i_j]. Thus r is a length-k subsequence of nums, preserving the original relative order.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_4
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      IsSubseq (toInts r.val) (toInts nums.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      IsSubseq (toInts r.val) (toInts nums.val)) := by
  sorry

/-- Whenever the function returns a result r, for every choice of indices j_0 < j_1 < ... < j_{k-1} with 0 <= j_t < len(nums), we have Sum(r) >= nums[j_0] + nums[j_1] + ... + nums[j_{k-1}], where Sum(r) is the mathematical sum of the elements of r. Equivalently, Sum(r) is the maximum possible sum of a length-k subsequence of nums.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_5
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ (f : Fin k.val.toNat → Fin nums.val.length), StrictMono f →
        sumI (List.ofFn (n := k.val.toNat) (fun j => (nums.val.get (f j)).val)) ≤
          sumI (toInts r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ (f : Fin k.val.toNat → Fin nums.val.length), StrictMono f →
        sumI (List.ofFn (n := k.val.toNat) (fun j => (nums.val.get (f j)).val)) ≤
          sumI (toInts r.val)) := by
  sorry

/-- Whenever the function returns a result r, let a_0 >= a_1 >= ... >= a_{len(nums)-1} be the elements of nums sorted in nonincreasing order with multiplicity preserved. Then Sum(r) = a_0 + a_1 + ... + a_{k-1}. In other words, Sum(r) is the sum of the k largest elements of nums, counted with multiplicity.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_6
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ a, IsDescOrdering a (toInts nums.val) →
        sumI (toInts r.val) = sumI (a.take k.val.toNat) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ a, IsDescOrdering a (toInts nums.val) →
        sumI (toInts r.val) = sumI (a.take k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, the multiset of elements of r is exactly the multiset of the k largest elements of nums counted with multiplicity. Equivalently, for every integer v, the number of occurrences of v in r equals the number of occurrences of v among the first k elements of a nonincreasing ordering of nums.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_7
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ a, IsDescOrdering a (toInts nums.val) →
        ∀ v, (toInts r.val).count v = (a.take k.val.toNat).count v := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∀ a, IsDescOrdering a (toInts nums.val) →
        ∀ v, (toInts r.val).count v = (a.take k.val.toNat).count v) := by
  sorry

/-- Whenever the function returns a result r, there exists a witnessing index sequence i_0 < ... < i_{k-1} with r[j] = nums[i_j] for all j, such that for every j in [0, k-1] and every b in [0, len(nums)-1] that is not equal to any i_t, we have nums[b] <= nums[i_j]. In words, every selected element is at least as large as every unselected element.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_8
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∃ f : Fin r.val.length → Fin nums.val.length,
        StrictMono f ∧
        (∀ j, r.val.get j = nums.val.get (f j)) ∧
        (∀ (j : Fin r.val.length) (b : Fin nums.val.length),
          (∀ t, f t ≠ b) → (nums.val.get b).val ≤ (nums.val.get (f j)).val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∃ f : Fin r.val.length → Fin nums.val.length,
        StrictMono f ∧
        (∀ j, r.val.get j = nums.val.get (f j)) ∧
        (∀ (j : Fin r.val.length) (b : Fin nums.val.length),
          (∀ t, f t ≠ b) → (nums.val.get b).val ≤ (nums.val.get (f j)).val)) := by
  sorry

/-- Let t be the k-th largest element of nums, counting multiplicity (so t is the element at index k-1 in a nonincreasing ordering of nums). Whenever the function returns a result r, for every j with 0 <= j < len(r), we have t <= r[j] <= max_{0 <= i < len(nums)} nums[i].
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_9
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∃ a, IsDescOrdering a (toInts nums.val) ∧
        ∃ (t M : Int), a[k.val.toNat - 1]? = some t ∧ IsMax M (toInts nums.val) ∧
          (∀ j : Fin r.val.length,
            t ≤ (r.val.get j).val ∧ (r.val.get j).val ≤ M) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      ∃ a, IsDescOrdering a (toInts nums.val) ∧
        ∃ (t M : Int), a[k.val.toNat - 1]? = some t ∧ IsMax M (toInts nums.val) ∧
          (∀ j : Fin r.val.length,
            t ≤ (r.val.get j).val ∧ (r.val.get j).val ≤ M)) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 1 and r[0] = max_{0 <= i < len(nums)} nums[i]. If the maximum value occurs multiple times, any occurrence may be chosen.
  Preconditions: 1 <= len(nums) <= 1000; k = 1; for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_10
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_k : k.val = 1)
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      r.val.length = 1 ∧ ∃ M, IsMax M (toInts nums.val) ∧ (toInts r.val)[0]? = some M := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_k : k.val = 1)
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      r.val.length = 1 ∧ ∃ M, IsMax M (toInts nums.val) ∧ (toInts r.val)[0]? = some M) := by
  sorry

/-- Whenever the function returns a result r, len(r) = len(nums) and for every j with 0 <= j < len(nums), r[j] = nums[j]. Thus r is exactly nums.
  Preconditions: 1 <= len(nums) <= 1000; k = len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_11
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_k : k.val = (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r → r.val = nums.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_k : k.val = (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r → r.val = nums.val) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < k, r[j] = nums[len(nums)-k+j]. Thus r is the suffix of nums of length k.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] <= nums[i+1]. -/
theorem spec_12
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (h_sorted : SortedAsc (toInts nums.val)) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      toInts r.val = (toInts nums.val).drop ((toInts nums.val).length - k.val.toNat) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (h_sorted : SortedAsc (toInts nums.val)), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      toInts r.val = (toInts nums.val).drop ((toInts nums.val).length - k.val.toNat)) := by
  sorry

/-- Whenever the function returns a result r, for every j with 0 <= j < k, r[j] = nums[j]. Thus r is the prefix of nums of length k.
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; for every i with 0 <= i < len(nums)-1, nums[i] >= nums[i+1]. -/
theorem spec_13
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (h_sorted : SortedDesc (toInts nums.val)) :
    ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      toInts r.val = (toInts nums.val).take k.val.toNat := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (h_sorted : SortedDesc (toInts nums.val)), ∀ r, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      toInts r.val = (toInts nums.val).take k.val.toNat) := by
  sorry

/-- For every slice p that is a permutation of nums (so len(p) = len(nums) and p has the same multiset of elements as nums), if max_subsequence(nums,k) returns r and max_subsequence(p,k) returns s, then for every integer v, the number of occurrences of v in r equals the number of occurrences of v in s. In particular, Sum(r) = Sum(s).
  Preconditions: 1 <= len(nums) <= 1000; 1 <= k <= len(nums); for every i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000. -/
theorem spec_14
    (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (p : Slice Std.I64) (h_perm : p.val.Perm nums.val) :
    ∀ r s, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      Aegis.MaxSubsequence.max_subsequence p k = ok s →
        (∀ v, (toInts r.val).count v = (toInts s.val).count v) ∧
        sumI (toInts r.val) = sumI (toInts s.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
    (h_npos : 1 ≤ nums.val.length)
    (h_nle : nums.val.length ≤ 1000)
    (h_kpos : 1 ≤ k.val)
    (h_kle : k.val ≤ (nums.val.length : Int))
    (h_bnd : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
    (p : Slice Std.I64) (h_perm : p.val.Perm nums.val), ∀ r s, Aegis.MaxSubsequence.max_subsequence nums k = ok r →
      Aegis.MaxSubsequence.max_subsequence p k = ok s →
        (∀ v, (toInts r.val).count v = (toInts s.val).count v) ∧
        sumI (toInts r.val) = sumI (toInts s.val)) := by
  sorry

end AegisSpec.MaxSubsequence
