import Aegis.FindMaximumXor.Code.Funs

/-!
# Specifications of `Aegis.FindMaximumXor.find_maximum_xor`

LeetCode problem `maximum-xor-of-two-numbers-in-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindMaximumXor

  def elem (nums : Slice I64) (i : ℕ) : ℤ := (nums.val.getD i 0#i64).val

  def xorInt (a b : ℤ) : ℤ := ((a.toNat ^^^ b.toNat : ℕ) : ℤ)

  def orAll (nums : Slice I64) : ℕ :=
    (nums.val.map (fun x => x.val.toNat)).foldr (fun a b => a ||| b) 0

  def maxEntry (nums : Slice I64) : ℤ := (nums.val.map (fun x => x.val)).foldr max 0

  def Occurs (nums : Slice I64) (v : ℤ) : Prop :=
    ∃ i, i < nums.val.length ∧ elem nums i = v

  def countOf (nums : Slice I64) (v : ℤ) : ℕ :=
    (nums.val.filter (fun x => decide (x.val = v))).length

  def hasBit (n k : ℕ) : Prop := n.testBit k = true

  /-- The function returns a result r, and r is the maximum of the set { nums[i] XOR nums[j] | 0 <= i <= j < len(nums) }, where XOR is bitwise exclusive-or on the 31-bit binary representations of the non-negative values. Equivalently: (1) for every i, j with 0 <= i <= j < len(nums), nums[i] XOR nums[j] <= r; and (2) there exist i, j with 0 <= i <= j < len(nums) such that r = nums[i] XOR nums[j].
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. Here nums[i] denotes the integer value stored in the i-th element of the slice. -/
  theorem spec_1 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∃ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r ∧
          (∀ i j, i ≤ j → j < nums.val.length →
              xorInt (elem nums i) (elem nums j) ≤ r.val) ∧
          (∃ i j, i ≤ j ∧ j < nums.val.length ∧
              r.val = xorInt (elem nums i) (elem nums j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∃ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r ∧
            (∀ i j, i ≤ j → j < nums.val.length →
                xorInt (elem nums i) (elem nums j) ≤ r.val) ∧
            (∃ i j, i ≤ j ∧ j < nums.val.length ∧
                r.val = xorInt (elem nums i) (elem nums j))) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic) on any input satisfying the preconditions.
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_2 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∃ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∃ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_3 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2147483647 (that is, r <= 2^31 - 1).
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_4 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r → r.val ≤ 2147483647 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64, Aegis.FindMaximumXor.find_maximum_xor nums = ok r → r.val ≤ 2147483647) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i <= j < len(nums) such that r = nums[i] XOR nums[j].
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_5 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
          ∃ i j, i ≤ j ∧ j < nums.val.length ∧
            r.val = xorInt (elem nums i) (elem nums j) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            ∃ i j, i ≤ j ∧ j < nums.val.length ∧
              r.val = xorInt (elem nums i) (elem nums j)) := by
    sorry

  /-- Whenever the function returns a result r, for every i and j with 0 <= i <= j < len(nums), nums[i] XOR nums[j] <= r.
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_6 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
          ∀ i j, i ≤ j → j < nums.val.length →
            xorInt (elem nums i) (elem nums j) ≤ r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            ∀ i j, i ≤ j → j < nums.val.length →
              xorInt (elem nums i) (elem nums j) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if all entries of nums are equal to one another (i.e., for all i, j with 0 <= i < len(nums) and 0 <= j < len(nums), nums[i] = nums[j]).
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_7 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
          (r.val = 0 ↔
            ∀ i j, i < nums.val.length → j < nums.val.length → elem nums i = elem nums j) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            (r.val = 0 ↔
              ∀ i j, i < nums.val.length → j < nums.val.length → elem nums i = elem nums j)) := by
    sorry

  /-- Whenever the function returns a result r, r is the maximum of the set { nums[i] XOR nums[j] | 0 <= i < j < len(nums) } (strictly distinct indices).
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647; there exist i, j with 0 <= i < len(nums) and 0 <= j < len(nums) such that nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
      (h_neq : ∃ i j, i < nums.val.length ∧ j < nums.val.length ∧ elem nums i ≠ elem nums j) :
      ∀ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
          (∀ i j, i < j → j < nums.val.length →
              xorInt (elem nums i) (elem nums j) ≤ r.val) ∧
            (∃ i j, i < j ∧ j < nums.val.length ∧
              r.val = xorInt (elem nums i) (elem nums j)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
        (h_neq : ∃ i j, i < nums.val.length ∧ j < nums.val.length ∧ elem nums i ≠ elem nums j), ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            (∀ i j, i < j → j < nums.val.length →
                xorInt (elem nums i) (elem nums j) ≤ r.val) ∧
              (∃ i j, i < j ∧ j < nums.val.length ∧
                r.val = xorInt (elem nums i) (elem nums j))) := by
    sorry

  /-- If there exists an index z with 0 <= z < len(nums) and nums[z] = 0, then whenever the function returns a result r, r >= M, where M is the maximum value among nums[0], ..., nums[len(nums)-1].
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_9 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      (∃ z, z < nums.val.length ∧ elem nums z = 0) →
        ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r → maxEntry nums ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), (∃ z, z < nums.val.length ∧ elem nums z = 0) →
          ∀ r : I64,
            Aegis.FindMaximumXor.find_maximum_xor nums = ok r → maxEntry nums ≤ r.val) := by
    sorry

  /-- If there exist indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums) such that nums[i] XOR nums[j] = 2147483647, then whenever the function returns a result r, r = 2147483647.
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_10 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      (∃ i j, i < nums.val.length ∧ j < nums.val.length ∧
          xorInt (elem nums i) (elem nums j) = 2147483647) →
        ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r → r.val = 2147483647 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), (∃ i j, i < nums.val.length ∧ j < nums.val.length ∧
            xorInt (elem nums i) (elem nums j) = 2147483647) →
          ∀ r : I64,
            Aegis.FindMaximumXor.find_maximum_xor nums = ok r → r.val = 2147483647) := by
    sorry

  /-- Let S(nums) be the set of distinct integer values that occur as entries of nums, and S(nums2) similarly. If S(nums) = S(nums2), then whenever find_maximum_xor(nums) returns r and find_maximum_xor(nums2) returns r2, we have r = r2.
    Preconditions: Both nums and nums2 are slices satisfying the problem constraints: len(nums) >= 1, len(nums2) >= 1, each length at most 200000, and every entry of either slice is in [0, 2147483647]. -/
  theorem spec_11 (nums nums2 : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
      (h_len2 : 1 ≤ nums2.val.length)
      (h_len2_ub : nums2.val.length ≤ 200000)
      (h_range2 : ∀ i, i < nums2.val.length → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 2147483647) :
      (∀ v : ℤ, Occurs nums v ↔ Occurs nums2 v) →
        ∀ r r2 : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            Aegis.FindMaximumXor.find_maximum_xor nums2 = ok r2 → r = r2 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
        (h_len2 : 1 ≤ nums2.val.length)
        (h_len2_ub : nums2.val.length ≤ 200000)
        (h_range2 : ∀ i, i < nums2.val.length → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 2147483647), (∀ v : ℤ, Occurs nums v ↔ Occurs nums2 v) →
          ∀ r r2 : I64,
            Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
              Aegis.FindMaximumXor.find_maximum_xor nums2 = ok r2 → r = r2) := by
    sorry

  /-- Whenever find_maximum_xor(nums) returns r and find_maximum_xor(nums2) returns r2, we have r <= r2.
    Preconditions: Both nums and nums2 satisfy the problem constraints: lengths at least 1 and at most 200000, and every entry is in [0, 2147483647]. Additionally, nums is a sub-multiset of nums2: for every value v, the number of occurrences of v in nums is at most the number of occurrences of v in nums2. -/
  theorem spec_12 (nums nums2 : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
      (h_len2 : 1 ≤ nums2.val.length)
      (h_len2_ub : nums2.val.length ≤ 200000)
      (h_range2 : ∀ i, i < nums2.val.length → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 2147483647) :
      (∀ v : ℤ, countOf nums v ≤ countOf nums2 v) →
        ∀ r r2 : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            Aegis.FindMaximumXor.find_maximum_xor nums2 = ok r2 → r.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647)
        (h_len2 : 1 ≤ nums2.val.length)
        (h_len2_ub : nums2.val.length ≤ 200000)
        (h_range2 : ∀ i, i < nums2.val.length → 0 ≤ elem nums2 i ∧ elem nums2 i ≤ 2147483647), (∀ v : ℤ, countOf nums v ≤ countOf nums2 v) →
          ∀ r r2 : I64,
            Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
              Aegis.FindMaximumXor.find_maximum_xor nums2 = ok r2 → r.val ≤ r2.val) := by
    sorry

  /-- Let O be the bitwise OR of all entries of nums, i.e., O = nums[0] OR nums[1] OR ... OR nums[len(nums)-1]. Whenever the function returns a result r, r is a bitwise submask of O: for every bit position k with 0 <= k < 31, if bit k of r is 1, then bit k of O is 1.
    Preconditions: len(nums) >= 1; len(nums) <= 200000; for every i with 0 <= i < len(nums), 0 <= nums[i] <= 2147483647. -/
  theorem spec_13 (nums : Slice I64)
      (h_len : 1 ≤ nums.val.length)
      (h_len_ub : nums.val.length ≤ 200000)
      (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647) :
      ∀ r : I64,
        Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
          ∀ k, k < 31 → hasBit r.val.toNat k → hasBit (orAll nums) k := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (h_len : 1 ≤ nums.val.length)
        (h_len_ub : nums.val.length ≤ 200000)
        (h_range : ∀ i, i < nums.val.length → 0 ≤ elem nums i ∧ elem nums i ≤ 2147483647), ∀ r : I64,
          Aegis.FindMaximumXor.find_maximum_xor nums = ok r →
            ∀ k, k < 31 → hasBit r.val.toNat k → hasBit (orAll nums) k) := by
    sorry

  end AegisSpec.FindMaximumXor
