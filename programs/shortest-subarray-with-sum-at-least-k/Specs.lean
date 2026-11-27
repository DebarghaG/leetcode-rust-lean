import Aegis.ShortestSubarray.Code.Funs

/-!
# Specifications of `Aegis.ShortestSubarray.shortest_subarray`

LeetCode problem `shortest-subarray-with-sum-at-least-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ShortestSubarray

  def intSum (l : List ℤ) : ℤ := l.foldl (fun acc x => acc + x) 0

  def rangeSum (l : List Std.I64) (a b : Nat) : ℤ :=
    intSum (((l.drop a).take (b + 1 - a)).map (fun x => x.val))

  def totalSum (l : List Std.I64) : ℤ := intSum (l.map (fun x => x.val))

  def hasWitness (l : List Std.I64) (K : ℤ) : Prop :=
    ∃ a b : Nat, a ≤ b ∧ b < l.length ∧ K ≤ rangeSum l a b

  def isMinLen (l : List Std.I64) (K : ℤ) (r : ℤ) : Prop :=
    (∃ a b : Nat, a ≤ b ∧ b < l.length ∧ K ≤ rangeSum l a b ∧
      r = (b : ℤ) + 1 - (a : ℤ)) ∧
    (∀ a b : Nat, a ≤ b → b < l.length → K ≤ rangeSum l a b →
      r ≤ (b : ℤ) + 1 - (a : ℤ))

  def padded (l : List Std.I64) (m n0 : Nat) : List Std.I64 :=
    List.replicate m 0#i64 ++ l ++ List.replicate n0 0#i64

  /-- The function returns a result r and: if there exist integers a and b with 0 <= a <= b < len(nums) and sum_{i=a}^{b} nums[i] >= k, then r = min{ b-a+1 | 0 <= a <= b < len(nums) and sum_{i=a}^{b} nums[i] >= k }; otherwise r = -1. Here the sum is the ordinary integer sum of the entries, and a subarray is non-empty and contiguous.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∃ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r ∧
        ((hasWitness nums.val k.val → isMinLen nums.val k.val r.val) ∧
         (¬ hasWitness nums.val k.val → r.val = -1)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∃ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r ∧
          ((hasWitness nums.val k.val → isMinLen nums.val k.val r.val) ∧
           (¬ hasWitness nums.val k.val → r.val = -1))) := by
    sorry

  /-- The function returns a result r; it does not fail (no arithmetic overflow, no out-of-bounds access, and no panic).
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∃ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∃ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= len(nums).
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ (nums.val.length : ℤ))) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, there exist integers a and b with 0 <= a <= b < len(nums), b-a+1 = r, and sum_{i=a}^{b} nums[i] >= k.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
        ∃ a b : Nat, a ≤ b ∧ b < nums.val.length ∧
          r.val = (b : ℤ) + 1 - (a : ℤ) ∧ k.val ≤ rangeSum nums.val a b := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
          ∃ a b : Nat, a ≤ b ∧ b < nums.val.length ∧
            r.val = (b : ℤ) + 1 - (a : ℤ) ∧ k.val ≤ rangeSum nums.val a b) := by
    sorry

  /-- Whenever the function returns a result r with r != -1, for every integers a and b with 0 <= a <= b < len(nums) and b-a+1 < r, sum_{i=a}^{b} nums[i] < k.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
        ∀ a b : Nat, a ≤ b → b < nums.val.length →
          (b : ℤ) + 1 - (a : ℤ) < r.val → rangeSum nums.val a b < k.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
          ∀ a b : Nat, a ≤ b → b < nums.val.length →
            (b : ℤ) + 1 - (a : ℤ) < r.val → rangeSum nums.val a b < k.val) := by
    sorry

  /-- Whenever the function returns a result r with r = -1, for every integers a and b with 0 <= a <= b < len(nums), sum_{i=a}^{b} nums[i] < k.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val = -1 →
        ∀ a b : Nat, a ≤ b → b < nums.val.length → rangeSum nums.val a b < k.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val = -1 →
          ∀ a b : Nat, a ≤ b → b < nums.val.length → rangeSum nums.val a b < k.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an integer i with 0 <= i < len(nums) and nums[i] >= k.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        (r.val = 1 ↔ ∃ x ∈ nums.val, k.val ≤ x.val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          (r.val = 1 ↔ ∃ x ∈ nums.val, k.val ≤ x.val)) := by
    sorry

  /-- Whenever the function returns a result r, if for every integer i with 0 <= i < len(nums), nums[i] <= 0, then r = -1.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        (∀ x ∈ nums.val, x.val ≤ 0) → r.val = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          (∀ x ∈ nums.val, x.val ≤ 0) → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r for (nums, k), if r != -1, then for every integer k' with 1 <= k' <= k, the set { b-a+1 | 0 <= a <= b < len(nums) and sum_{i=a}^{b} nums[i] >= k' } is nonempty and its minimum is at most r.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
        ∀ k' : ℤ, 1 ≤ k' → k' ≤ k.val →
          hasWitness nums.val k' ∧
          (∃ a b : Nat, a ≤ b ∧ b < nums.val.length ∧ k' ≤ rangeSum nums.val a b ∧
            (b : ℤ) + 1 - (a : ℤ) ≤ r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r → r.val ≠ -1 →
          ∀ k' : ℤ, 1 ≤ k' → k' ≤ k.val →
            hasWitness nums.val k' ∧
            (∃ a b : Nat, a ≤ b ∧ b < nums.val.length ∧ k' ≤ rangeSum nums.val a b ∧
              (b : ℤ) + 1 - (a : ℤ) ≤ r.val)) := by
    sorry

  /-- Let nums' be the sequence of length len(nums)+m+n0 such that nums'[i] = 0 for 0 <= i < m, nums'[m+i] = nums[i] for 0 <= i < len(nums), and nums'[m+len(nums)+j] = 0 for 0 <= j < n0. Whenever the function returns a result r for (nums, k), if there exist integers a and b with 0 <= a <= b < len(nums') and sum_{i=a}^{b} nums'[i] >= k, then r = min{ b-a+1 | 0 <= a <= b < len(nums') and sum_{i=a}^{b} nums'[i] >= k }; otherwise r = -1.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000; m and n0 are non-negative integers with len(nums)+m+n0 <= 100000. -/
  theorem spec_10 (nums : Slice Std.I64) (k : Std.I64) (m n0 : Nat)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
      (hpad : nums.val.length + m + n0 ≤ 100000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        ((hasWitness (padded nums.val m n0) k.val →
            isMinLen (padded nums.val m n0) k.val r.val) ∧
         (¬ hasWitness (padded nums.val m n0) k.val → r.val = -1)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64) (m n0 : Nat)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000)
        (hpad : nums.val.length + m + n0 ≤ 100000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          ((hasWitness (padded nums.val m n0) k.val →
              isMinLen (padded nums.val m n0) k.val r.val) ∧
           (¬ hasWitness (padded nums.val m n0) k.val → r.val = -1))) := by
    sorry

  /-- Whenever the function returns a result r, if for every integer i with 0 <= i < len(nums), nums[i] > 0, and sum_{i=0}^{len(nums)-1} nums[i] < k, then r = -1.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        (∀ x ∈ nums.val, 0 < x.val) → totalSum nums.val < k.val → r.val = -1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          (∀ x ∈ nums.val, 0 < x.val) → totalSum nums.val < k.val → r.val = -1) := by
    sorry

  /-- Whenever the function returns a result r, if r = len(nums), then sum_{i=0}^{len(nums)-1} nums[i] >= k.
    Preconditions: 1 <= len(nums) <= 100000; for every integer i with 0 <= i < len(nums), -100000 <= nums[i] <= 100000; 1 <= k <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64) (k : Std.I64)
      (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
      (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
      (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000) :
      ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
        r.val = (nums.val.length : ℤ) → k.val ≤ totalSum nums.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (k : Std.I64)
        (hlen1 : 1 ≤ nums.val.length) (hlen2 : nums.val.length ≤ 100000)
        (helem : ∀ x ∈ nums.val, -100000 ≤ x.val ∧ x.val ≤ 100000)
        (hk1 : 1 ≤ k.val) (hk2 : k.val ≤ 1000000000), ∀ r, Aegis.ShortestSubarray.shortest_subarray nums k = ok r →
          r.val = (nums.val.length : ℤ) → k.val ≤ totalSum nums.val) := by
    sorry

  end AegisSpec.ShortestSubarray
