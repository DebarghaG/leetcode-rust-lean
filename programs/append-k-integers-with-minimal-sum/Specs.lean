import Aegis.MinimalKSum.Code.Funs

/-!
# Specifications of `Aegis.MinimalKSum.minimal_k_sum`

LeetCode problem `append-k-integers-with-minimal-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.MinimalKSum

  namespace AegisSpec.MinimalKSum

  def entries (nums : Slice Std.I64) : List ℤ := nums.val.map (fun y => y.val)

  def OccursIn (nums : Slice Std.I64) (x : ℤ) : Prop := x ∈ entries nums

  noncomputable def missingUpTo (nums : Slice Std.I64) (N : ℕ) : Finset ℕ :=
    by classical exact (Finset.range N).filter (fun j => ¬ OccursIn nums ((j : ℤ) + 1))

  noncomputable def occursUpTo (nums : Slice Std.I64) (m : ℤ) : Finset ℤ :=
    by
      classical exact
        (entries nums).toFinset.filter (fun d => 1 ≤ d ∧ d ≤ m)

  def IsKthMissing (nums : Slice Std.I64) (k : ℤ) (m : ℤ) : Prop :=
    0 < m ∧ ¬ OccursIn nums m ∧ (missingUpTo nums (m - 1).toNat).card = k.toNat - 1

  def IsKSmallestMissing (nums : Slice Std.I64) (k : ℤ) (A : Finset ℤ) : Prop :=
    A.card = k.toNat ∧
    (∀ a ∈ A, 0 < a ∧ ¬ OccursIn nums a) ∧
    (∀ x : ℤ, 0 < x → ¬ OccursIn nums x → x ∉ A → ∀ a ∈ A, a < x)

  /-- Whenever minimal_k_sum(nums, k) returns a result r, let a_1 < a_2 < ... < a_k be the k smallest positive integers x such that no index i with 0 <= i < len(nums) has nums[i] = x. Then r = a_1 + a_2 + ... + a_k.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. All arithmetic in the statement is mathematical integer arithmetic. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      ∃ A : Finset ℤ, IsKSmallestMissing nums k.val A ∧ r.val = ∑ a ∈ A, a := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), ∃ A : Finset ℤ, IsKSmallestMissing nums k.val A ∧ r.val = ∑ a ∈ A, a) := by
    sorry

  /-- For every input satisfying the preconditions, minimal_k_sum(nums, k) returns a result r; it does not fail, panic, go out of bounds, or overflow.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000) :
      ∃ r : Std.I64, minimal_k_sum nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000), ∃ r : Std.I64, minimal_k_sum nums k = ok r) := by
    sorry

  /-- Whenever minimal_k_sum(nums, k) returns a result r, r >= k*(k+1)/2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      k.val * (k.val + 1) / 2 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), k.val * (k.val + 1) / 2 ≤ r.val) := by
    sorry

  /-- Whenever minimal_k_sum(nums, k) returns a result r, r <= k*len(nums) + k*(k+1)/2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      r.val ≤ k.val * (nums.val.length : ℤ) + k.val * (k.val + 1) / 2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), r.val ≤ k.val * (nums.val.length : ℤ) + k.val * (k.val + 1) / 2) := by
    sorry

  /-- Let m be the k-th smallest positive integer that does not occur in nums. Whenever minimal_k_sum(nums, k) returns a result r, r = m*(m+1)/2 - sum of d over the set D, where D is the set of distinct integers d such that 1 <= d <= m and there exists i with 0 <= i < len(nums) and nums[i] = d.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      ∃ m : ℤ, IsKthMissing nums k.val m ∧
        r.val = m * (m + 1) / 2 - ∑ d ∈ occursUpTo nums m, d := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), ∃ m : ℤ, IsKthMissing nums k.val m ∧
          r.val = m * (m + 1) / 2 - ∑ d ∈ occursUpTo nums m, d) := by
    sorry

  /-- Suppose there is an integer a with 0 <= a such that every integer 1,2,...,a occurs as some nums[i], and no integer a+1,a+2,...,a+k occurs as any nums[i]. Then whenever minimal_k_sum(nums, k) returns a result r, r = k*(2*a+k+1)/2, equivalently r = sum from j=1 to k of (a+j).
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      (a : ℤ) (ha : 0 ≤ a)
      (ha_occ : ∀ x : ℤ, 1 ≤ x → x ≤ a → OccursIn nums x)
      (ha_miss : ∀ x : ℤ, a + 1 ≤ x → x ≤ a + k.val → ¬ OccursIn nums x)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      r.val = k.val * (2 * a + k.val + 1) / 2 ∧
        r.val = ∑ j ∈ Finset.range k.val.toNat, (a + ((j : ℤ) + 1)) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        (a : ℤ) (ha : 0 ≤ a)
        (ha_occ : ∀ x : ℤ, 1 ≤ x → x ≤ a → OccursIn nums x)
        (ha_miss : ∀ x : ℤ, a + 1 ≤ x → x ≤ a + k.val → ¬ OccursIn nums x)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), r.val = k.val * (2 * a + k.val + 1) / 2 ∧
          r.val = ∑ j ∈ Finset.range k.val.toNat, (a + ((j : ℤ) + 1))) := by
    sorry

  /-- If every positive integer that occurs as an entry of nums1 also occurs as an entry of nums2, then whenever minimal_k_sum(nums1, k) returns r1 and minimal_k_sum(nums2, k) returns r2, r1 <= r2.
    Preconditions: nums1 and nums2 are slices of 64-bit integers, each with 1 <= length <= 100000 and all entries between 1 and 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen1_pos : 1 ≤ nums1.val.length) (hlen1_le : nums1.val.length ≤ 100000)
      (hentries1 : ∀ y ∈ nums1.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
      (hentries2 : ∀ y ∈ nums2.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      (hsub : ∀ x : ℤ, 0 < x → OccursIn nums1 x → OccursIn nums2 x)
      {r1 r2 : Std.I64} (h1 : minimal_k_sum nums1 k = ok r1)
      (h2 : minimal_k_sum nums2 k = ok r2) :
      r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen1_pos : 1 ≤ nums1.val.length) (hlen1_le : nums1.val.length ≤ 100000)
        (hentries1 : ∀ y ∈ nums1.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
        (hentries2 : ∀ y ∈ nums2.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        (hsub : ∀ x : ℤ, 0 < x → OccursIn nums1 x → OccursIn nums2 x)
        {r1 r2 : Std.I64} (h1 : minimal_k_sum nums1 k = ok r1)
        (h2 : minimal_k_sum nums2 k = ok r2), r1.val ≤ r2.val) := by
    sorry

  /-- If, for every positive integer x, x occurs as an entry of nums1 if and only if x occurs as an entry of nums2, then whenever minimal_k_sum(nums1, k) returns r1 and minimal_k_sum(nums2, k) returns r2, r1 = r2.
    Preconditions: nums1 and nums2 are slices of 64-bit integers, each with 1 <= length <= 100000 and all entries between 1 and 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_8 (nums1 nums2 : Slice Std.I64) (k : Std.I64)
      (hlen1_pos : 1 ≤ nums1.val.length) (hlen1_le : nums1.val.length ≤ 100000)
      (hentries1 : ∀ y ∈ nums1.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
      (hentries2 : ∀ y ∈ nums2.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      (hsame : ∀ x : ℤ, 0 < x → (OccursIn nums1 x ↔ OccursIn nums2 x))
      {r1 r2 : Std.I64} (h1 : minimal_k_sum nums1 k = ok r1)
      (h2 : minimal_k_sum nums2 k = ok r2) :
      r1.val = r2.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (k : Std.I64)
        (hlen1_pos : 1 ≤ nums1.val.length) (hlen1_le : nums1.val.length ≤ 100000)
        (hentries1 : ∀ y ∈ nums1.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hlen2_pos : 1 ≤ nums2.val.length) (hlen2_le : nums2.val.length ≤ 100000)
        (hentries2 : ∀ y ∈ nums2.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        (hsame : ∀ x : ℤ, 0 < x → (OccursIn nums1 x ↔ OccursIn nums2 x))
        {r1 r2 : Std.I64} (h1 : minimal_k_sum nums1 k = ok r1)
        (h2 : minimal_k_sum nums2 k = ok r2), r1.val = r2.val) := by
    sorry

  /-- Whenever minimal_k_sum(nums, k) returns a result r, r = k*(k+1)/2 if and only if no value x with 1 <= x <= k occurs as an entry of nums.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      (r.val = k.val * (k.val + 1) / 2 ↔
        ∀ x : ℤ, 1 ≤ x → x ≤ k.val → ¬ OccursIn nums x) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), (r.val = k.val * (k.val + 1) / 2 ↔
          ∀ x : ℤ, 1 ≤ x → x ≤ k.val → ¬ OccursIn nums x)) := by
    sorry

  /-- Whenever minimal_k_sum(nums, k) returns a result r, there exists a finite set A of positive integers such that |A| = k, no element of A is equal to any nums[i], the sum of all a in A equals r, and every positive integer x that is not in A and does not occur in nums is greater than every element of A.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k is a 64-bit integer with 1 <= k <= 100000000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
      {r : Std.I64} (hr : minimal_k_sum nums k = ok r) :
      ∃ A : Finset ℤ, A.card = k.val.toNat ∧
        (∀ a ∈ A, 0 < a) ∧
        (∀ a ∈ A, ¬ OccursIn nums a) ∧
        (∑ a ∈ A, a) = r.val ∧
        (∀ x : ℤ, 0 < x → ¬ OccursIn nums x → x ∉ A → ∀ a ∈ A, a < x) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 100000000)
        {r : Std.I64} (hr : minimal_k_sum nums k = ok r), ∃ A : Finset ℤ, A.card = k.val.toNat ∧
          (∀ a ∈ A, 0 < a) ∧
          (∀ a ∈ A, ¬ OccursIn nums a) ∧
          (∑ a ∈ A, a) = r.val ∧
          (∀ x : ℤ, 0 < x → ¬ OccursIn nums x → x ∉ A → ∀ a ∈ A, a < x)) := by
    sorry

  /-- Whenever minimal_k_sum(nums, k1) returns r1 and minimal_k_sum(nums, k2) returns r2, r1 <= r2. Moreover, if k1 < k2 then r1 < r2.
    Preconditions: nums is a slice of 64-bit integers with 1 <= len(nums) <= 100000 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000; k1 and k2 are 64-bit integers with 1 <= k1 <= k2 <= 100000000. -/
  theorem spec_11 (nums : Slice Std.I64) (k1 k2 : Std.I64)
      (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
      (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
      (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 100000000)
      {r1 r2 : Std.I64} (h1 : minimal_k_sum nums k1 = ok r1)
      (h2 : minimal_k_sum nums k2 = ok r2) :
      r1.val ≤ r2.val ∧ (k1.val < k2.val → r1.val < r2.val) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k1 k2 : Std.I64)
        (hlen_pos : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 100000)
        (hentries : ∀ y ∈ nums.val, 1 ≤ y.val ∧ y.val ≤ 1000000000)
        (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 100000000)
        {r1 r2 : Std.I64} (h1 : minimal_k_sum nums k1 = ok r1)
        (h2 : minimal_k_sum nums k2 = ok r2), r1.val ≤ r2.val ∧ (k1.val < k2.val → r1.val < r2.val)) := by
    sorry

  end AegisSpec.MinimalKSum
