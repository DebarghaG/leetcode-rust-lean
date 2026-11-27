import Aegis.CanPartition.Code.Funs

/-!
# Specifications of `Aegis.CanPartition.can_partition`

LeetCode problem `partition-equal-subset-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CanPartition

  def elem (nums : Slice Std.I64) (i : Nat) : Int :=
    match nums.val[i]? with
    | some x => x.val
    | none => 0

  def idxSum (nums : Slice Std.I64) (s : Finset Nat) : Int :=
    ∑ i ∈ s, elem nums i

  def total (nums : Slice Std.I64) : Int :=
    idxSum nums (Finset.range nums.val.length)

  def i64OfInt (k : Int) : Std.I64 := ⟨BitVec.ofInt 64 k⟩

  /-- Whenever can_partition(nums) returns a result r, r = true if and only if there exist sets A and B of indices from {0, 1, ..., len(nums)-1} such that A intersect B is empty, A union B = {0, 1, ..., len(nums)-1}, and sum_{i in A} nums[i] = sum_{i in B} nums[i] (all sums exact integers).
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_1 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      (r = true ↔
        ∃ A B : Finset Nat,
          A ⊆ Finset.range nums.val.length ∧
          B ⊆ Finset.range nums.val.length ∧
          Disjoint A B ∧
          A ∪ B = Finset.range nums.val.length ∧
          idxSum nums A = idxSum nums B) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hr : Aegis.CanPartition.can_partition nums = ok r), (r = true ↔
          ∃ A B : Finset Nat,
            A ⊆ Finset.range nums.val.length ∧
            B ⊆ Finset.range nums.val.length ∧
            Disjoint A B ∧
            A ∪ B = Finset.range nums.val.length ∧
            idxSum nums A = idxSum nums B)) := by
    sorry

  /-- can_partition(nums) returns a result r (a Bool) and does not fail; in particular, no i64 overflow or panic occurs.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100) :
      ∃ r : Bool, Aegis.CanPartition.can_partition nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100), ∃ r : Bool, Aegis.CanPartition.can_partition nums = ok r) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, if T = sum_{i=0}^{len(nums)-1} nums[i] is odd, then r = false.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_3 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      Odd (total nums) → r = false := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hr : Aegis.CanPartition.can_partition nums = ok r), Odd (total nums) → r = false) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, if r = true then for every i with 0 <= i < len(nums) we have 2 * nums[i] <= T, where T = sum_{j=0}^{len(nums)-1} nums[j].
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_4 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      r = true → ∀ i, i < nums.val.length → 2 * elem nums i ≤ total nums := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hr : Aegis.CanPartition.can_partition nums = ok r), r = true → ∀ i, i < nums.val.length → 2 * elem nums i ≤ total nums) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, if there exists an index i with 0 <= i < len(nums) and 2 * nums[i] = T, where T = sum_{j=0}^{len(nums)-1} nums[j], then r = true.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100. -/
  theorem spec_5 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      (∃ i, i < nums.val.length ∧ 2 * elem nums i = total nums) → r = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hr : Aegis.CanPartition.can_partition nums = ok r), (∃ i, i < nums.val.length ∧ 2 * elem nums i = total nums) → r = true) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, r = false.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; additionally len(nums) = 1. -/
  theorem spec_6 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hlen : nums.val.length = 1)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      r = false := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hlen : nums.val.length = 1)
        (hr : Aegis.CanPartition.can_partition nums = ok r), r = false) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, r = true if and only if nums[0] = nums[1].
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; additionally len(nums) = 2. -/
  theorem spec_7 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hlen : nums.val.length = 2)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      (r = true ↔ elem nums 0 = elem nums 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hlen : nums.val.length = 2)
        (hr : Aegis.CanPartition.can_partition nums = ok r), (r = true ↔ elem nums 0 = elem nums 1)) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, r = true if and only if there exists i with 0 <= i < 3 and 2 * nums[i] = T, where T = nums[0] + nums[1] + nums[2].
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; additionally len(nums) = 3. -/
  theorem spec_8 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hlen : nums.val.length = 3)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      (r = true ↔ ∃ i, i < 3 ∧ 2 * elem nums i = total nums) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hlen : nums.val.length = 3)
        (hr : Aegis.CanPartition.can_partition nums = ok r), (r = true ↔ ∃ i, i < 3 ∧ 2 * elem nums i = total nums)) := by
    sorry

  /-- Whenever can_partition(nums) returns a result r, r = true if and only if len(nums) is even.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; additionally there exists a positive integer c such that nums[i] = c for every i with 0 <= i < len(nums). -/
  theorem spec_9 (nums : Slice Std.I64) (r : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hconst : ∃ c : Int, 0 < c ∧ ∀ i, i < nums.val.length → elem nums i = c)
      (hr : Aegis.CanPartition.can_partition nums = ok r) :
      (r = true ↔ Even nums.val.length) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (r : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hconst : ∃ c : Int, 0 < c ∧ ∀ i, i < nums.val.length → elem nums i = c)
        (hr : Aegis.CanPartition.can_partition nums = ok r), (r = true ↔ Even nums.val.length)) := by
    sorry

  /-- If can_partition(nums) returns a result r and can_partition(perm) returns a result r', then r = r'.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; perm is any slice satisfying the same constraints that is a permutation of nums (same multiset of values, possibly different order). -/
  theorem spec_10 (nums perm : Slice Std.I64) (r r' : Bool)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (plen_ge : 1 ≤ perm.val.length) (plen_le : perm.val.length ≤ 200)
      (ppos : ∀ i, i < perm.val.length → 1 ≤ elem perm i ∧ elem perm i ≤ 100)
      (hperm : List.Perm nums.val perm.val)
      (hr : Aegis.CanPartition.can_partition nums = ok r)
      (hr' : Aegis.CanPartition.can_partition perm = ok r') :
      r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums perm : Slice Std.I64) (r r' : Bool)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (plen_ge : 1 ≤ perm.val.length) (plen_le : perm.val.length ≤ 200)
        (ppos : ∀ i, i < perm.val.length → 1 ≤ elem perm i ∧ elem perm i ≤ 100)
        (hperm : List.Perm nums.val perm.val)
        (hr : Aegis.CanPartition.can_partition nums = ok r)
        (hr' : Aegis.CanPartition.can_partition perm = ok r'), r = r') := by
    sorry

  /-- Let nums2 be the slice with nums2[i] = nums[i] / d for 0 <= i < len(nums). If can_partition(nums) returns a result r and can_partition(nums2) returns a result r', then r = r'.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; d is a positive integer such that d divides nums[i] for every i with 0 <= i < len(nums). -/
  theorem spec_11 (nums nums2 : Slice Std.I64) (r r' : Bool) (d : Int)
      (hd : 0 < d)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hdiv : ∀ i, i < nums.val.length → d ∣ elem nums i)
      (hnums2 : nums2.val = nums.val.map (fun x => i64OfInt (x.val / d)))
      (hr : Aegis.CanPartition.can_partition nums = ok r)
      (hr' : Aegis.CanPartition.can_partition nums2 = ok r') :
      r = r' := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (r r' : Bool) (d : Int)
        (hd : 0 < d)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hdiv : ∀ i, i < nums.val.length → d ∣ elem nums i)
        (hnums2 : nums2.val = nums.val.map (fun x => i64OfInt (x.val / d)))
        (hr : Aegis.CanPartition.can_partition nums = ok r)
        (hr' : Aegis.CanPartition.can_partition nums2 = ok r'), r = r') := by
    sorry

  /-- Let nums2 be the slice with nums2[i] = c * nums[i] for 0 <= i < len(nums). If can_partition(nums) returns a result r and can_partition(nums2) returns a result r', then r = r'.
    Preconditions: nums is a slice of 64-bit signed integers with 1 <= len(nums) <= 200 and, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 100; c is a positive integer such that c * nums[i] <= 100 for every i with 0 <= i < len(nums). -/
  theorem spec_12 (nums nums2 : Slice Std.I64) (r r' : Bool) (c : Int)
      (hc : 0 < c)
      (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
      (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
      (hmul : ∀ i, i < nums.val.length → c * elem nums i ≤ 100)
      (hnums2 : nums2.val = nums.val.map (fun x => i64OfInt (c * x.val)))
      (hr : Aegis.CanPartition.can_partition nums = ok r)
      (hr' : Aegis.CanPartition.can_partition nums2 = ok r') :
      r = r' := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums nums2 : Slice Std.I64) (r r' : Bool) (c : Int)
        (hc : 0 < c)
        (hlen_ge : 1 ≤ nums.val.length) (hlen_le : nums.val.length ≤ 200)
        (hpos : ∀ i, i < nums.val.length → 1 ≤ elem nums i ∧ elem nums i ≤ 100)
        (hmul : ∀ i, i < nums.val.length → c * elem nums i ≤ 100)
        (hnums2 : nums2.val = nums.val.map (fun x => i64OfInt (c * x.val)))
        (hr : Aegis.CanPartition.can_partition nums = ok r)
        (hr' : Aegis.CanPartition.can_partition nums2 = ok r'), r = r') := by
    sorry

  end AegisSpec.CanPartition
