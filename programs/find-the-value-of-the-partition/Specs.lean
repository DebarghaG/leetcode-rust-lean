import Aegis.FindValueOfPartition.Code.Funs

/-!
# Specifications of `Aegis.FindValueOfPartition.find_value_of_partition`

LeetCode problem `find-the-value-of-the-partition`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindValueOfPartition

  open Aeneas Aeneas.Std Result Aegis.FindValueOfPartition

  def intVals (nums : Slice I64) : List ℤ := nums.val.map (fun x => x.val)

  def listMax : List ℤ → ℤ
    | [] => 0
    | x :: xs => List.foldr max x xs

  def listMin : List ℤ → ℤ
    | [] => 0
    | x :: xs => List.foldr min x xs

  def IsPartition (l l1 l2 : List ℤ) : Prop :=
    l1 ≠ [] ∧ l2 ≠ [] ∧ List.Perm (l1 ++ l2) l

  def partitionValues (l : List ℤ) : Set ℤ :=
    {x | ∃ l1 l2 : List ℤ, IsPartition l l1 l2 ∧ x = |listMax l1 - listMin l2|}

  def pairValues (l : List ℤ) : Set ℤ :=
    {x | ∃ (i j : ℕ) (a b : ℤ), i < j ∧ l[i]? = some a ∧ l[j]? = some b ∧ x = |a - b|}

  def gapValues (l : List ℤ) : Set ℤ :=
    {x | ∃ (k : ℕ) (a b : ℤ), l[k]? = some a ∧ l[k+1]? = some b ∧ x = b - a}

  def Nondecreasing (l : List ℤ) : Prop :=
    ∀ (k : ℕ) (a b : ℤ), l[k]? = some a → l[k+1]? = some b → a ≤ b

  def HasDuplicate (l : List ℤ) : Prop :=
    ∃ (i j : ℕ) (a : ℤ), i < j ∧ l[i]? = some a ∧ l[j]? = some a

  /-- The function returns a result r, and r is the minimum value of |max(nums1) - min(nums2)| over all partitions of nums into two nonempty arrays nums1 and nums2, where a partition means every index i with 0 <= i < len(nums) is assigned to exactly one of nums1 or nums2, and nums1 and nums2 contain no other elements (their order is irrelevant).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, find_value_of_partition nums = ok r ∧
        IsLeast (partitionValues (intVals nums)) r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, find_value_of_partition nums = ok r ∧
          IsLeast (partitionValues (intVals nums)) r.val) := by
    sorry

  /-- The function returns a result r (and does not fail by overflow, out-of-bounds access, or panic) for every nums satisfying the preconditions.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∃ r, find_value_of_partition nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∃ r, find_value_of_partition nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r → 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r → 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= (max_{0 <= i < len(nums)} nums[i]) - (min_{0 <= i < len(nums)} nums[i]).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        r.val ≤ listMax (intVals nums) - listMin (intVals nums) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          r.val ≤ listMax (intVals nums) - listMin (intVals nums)) := by
    sorry

  /-- Whenever the function returns a result r, there exists a partition of nums into two nonempty arrays nums1 and nums2 such that r = |max(nums1) - min(nums2)|.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        ∃ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 ∧
          r.val = |listMax l1 - listMin l2| := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          ∃ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 ∧
            r.val = |listMax l1 - listMin l2|) := by
    sorry

  /-- Whenever the function returns a result r, r = min{ |nums[i] - nums[j]| : 0 <= i < j < len(nums) }.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        IsLeast (pairValues (intVals nums)) r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          IsLeast (pairValues (intVals nums)) r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices i and j with 0 <= i < j < len(nums) such that r = |nums[i] - nums[j]|.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        ∃ (i j : ℕ) (a b : ℤ), i < j ∧ (intVals nums)[i]? = some a ∧
          (intVals nums)[j]? = some b ∧ r.val = |a - b| := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          ∃ (i j : ℕ) (a b : ℤ), i < j ∧ (intVals nums)[i]? = some a ∧
            (intVals nums)[j]? = some b ∧ r.val = |a - b|) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there exist indices i and j with 0 <= i < j < len(nums) and nums[i] = nums[j].
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        (r.val = 0 ↔ HasDuplicate (intVals nums)) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          (r.val = 0 ↔ HasDuplicate (intVals nums))) := by
    sorry

  /-- Whenever the function returns results r for nums and r' for nums', r' = r.
    Preconditions: nums and nums' are slices with 2 <= len(nums) = len(nums') <= 100000 and all entries in [1, 1000000000]; nums' is a permutation of nums (same length and same multiset of entries). -/
  theorem spec_9 (nums nums' : Slice I64)
      (hlen : 2 ≤ nums.val.length)
      (hlen_eq : nums'.val.length = nums.val.length)
      (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hperm : List.Perm (intVals nums') (intVals nums)) :
      ∀ r r', find_value_of_partition nums = ok r →
        find_value_of_partition nums' = ok r' → r'.val = r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlen : 2 ≤ nums.val.length)
        (hlen_eq : nums'.val.length = nums.val.length)
        (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hperm : List.Perm (intVals nums') (intVals nums)), ∀ r r', find_value_of_partition nums = ok r →
          find_value_of_partition nums' = ok r' → r'.val = r.val) := by
    sorry

  /-- Whenever the function returns results r for nums and r' for nums', r' = c * r.
    Preconditions: nums is valid: 2 <= len(nums) <= 100000 and all entries lie in [1, 1000000000]; c is a positive integer and nums' is a slice with len(nums') = len(nums) and nums'[i] = c * nums[i] for all i, and nums' also satisfies 1 <= nums'[i] <= 1000000000 for all i. -/
  theorem spec_10 (nums nums' : Slice I64) (c : ℤ)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hc : 0 < c)
      (hlen_eq : nums'.val.length = nums.val.length)
      (hscale : ∀ (i : ℕ) (a : ℤ), (intVals nums)[i]? = some a →
        (intVals nums')[i]? = some (c * a))
      (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r r', find_value_of_partition nums = ok r →
        find_value_of_partition nums' = ok r' → r'.val = c * r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64) (c : ℤ)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hc : 0 < c)
        (hlen_eq : nums'.val.length = nums.val.length)
        (hscale : ∀ (i : ℕ) (a : ℤ), (intVals nums)[i]? = some a →
          (intVals nums')[i]? = some (c * a))
        (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r r', find_value_of_partition nums = ok r →
          find_value_of_partition nums' = ok r' → r'.val = c * r.val) := by
    sorry

  /-- Whenever the function returns results r for nums and r' for nums', r' <= r.
    Preconditions: nums and nums' are slices with 2 <= len(nums) < len(nums') <= 100000 and all entries in [1, 1000000000]; the multiset of entries of nums is a sub-multiset of the multiset of entries of nums' with at least one extra element (equivalently, nums' can be obtained from nums by inserting one or more additional elements). -/
  theorem spec_11 (nums nums' : Slice I64)
      (hlen : 2 ≤ nums.val.length)
      (hlen_lt : nums.val.length < nums'.val.length)
      (hlen_ub : nums'.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hsubperm : ∃ extra : List ℤ, extra ≠ [] ∧
        List.Perm (intVals nums ++ extra) (intVals nums')) :
      ∀ r r', find_value_of_partition nums = ok r →
        find_value_of_partition nums' = ok r' → r'.val ≤ r.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlen : 2 ≤ nums.val.length)
        (hlen_lt : nums.val.length < nums'.val.length)
        (hlen_ub : nums'.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hbounds' : ∀ x ∈ nums'.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hsubperm : ∃ extra : List ℤ, extra ≠ [] ∧
          List.Perm (intVals nums ++ extra) (intVals nums')), ∀ r r', find_value_of_partition nums = ok r →
          find_value_of_partition nums' = ok r' → r'.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = min{ sorted[k+1] - sorted[k] : 0 <= k < len(nums)-1 }.
    Preconditions: nums is valid: 2 <= len(nums) <= 100000 and all entries lie in [1, 1000000000]; sorted is a nondecreasing rearrangement of nums, i.e. len(sorted) = len(nums), sorted[k] <= sorted[k+1] for 0 <= k < len(nums)-1, and sorted has the same multiset of entries as nums. -/
  theorem spec_12 (nums sorted : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
      (hlen_eq : sorted.val.length = nums.val.length)
      (hsorted : Nondecreasing (intVals sorted))
      (hperm : List.Perm (intVals sorted) (intVals nums)) :
      ∀ r, find_value_of_partition nums = ok r →
        IsLeast (gapValues (intVals sorted)) r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums sorted : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000)
        (hlen_eq : sorted.val.length = nums.val.length)
        (hsorted : Nondecreasing (intVals sorted))
        (hperm : List.Perm (intVals sorted) (intVals nums)), ∀ r, find_value_of_partition nums = ok r →
          IsLeast (gapValues (intVals sorted)) r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists a partition of nums into two nonempty arrays nums1 and nums2 such that r = |max(nums1) - min(nums2)| and every element of nums1 is <= every element of nums2 (equivalently max(nums1) <= min(nums2)).
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_13 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        ∃ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 ∧
          listMax l1 ≤ listMin l2 ∧ r.val = |listMax l1 - listMin l2| := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          ∃ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 ∧
            listMax l1 ≤ listMin l2 ∧ r.val = |listMax l1 - listMin l2|) := by
    sorry

  /-- Whenever the function returns a result r, for every partition of nums into two nonempty arrays nums1 and nums2, r <= |max(nums1) - min(nums2)|.
    Preconditions: 2 <= len(nums) <= 100000 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000000000. -/
  theorem spec_14 (nums : Slice I64)
      (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000) :
      ∀ r, find_value_of_partition nums = ok r →
        ∀ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 →
          r.val ≤ |listMax l1 - listMin l2| := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hbounds : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000000), ∀ r, find_value_of_partition nums = ok r →
          ∀ l1 l2 : List ℤ, IsPartition (intVals nums) l1 l2 →
            r.val ≤ |listMax l1 - listMin l2|) := by
    sorry

  end AegisSpec.FindValueOfPartition
