import Aegis.PartitionDisjoint.Code.Funs

/-!
# Specifications of `Aegis.PartitionDisjoint.partition_disjoint`

LeetCode problem `partition-array-into-disjoint-intervals`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.PartitionDisjoint

  set_option autoImplicit false

  namespace AegisSpec.PartitionDisjoint

  def i64_min : Int := -(2 ^ 63)

  def i64_max : Int := 2 ^ 63 - 1

  def split_valid (nums : Slice Std.I64) (k : Nat) : Prop :=
    ∀ (i j : Nat) (_ : i < k) (_ : k ≤ j) (_ : j < nums.val.length),
      (nums.val[i]).val ≤ (nums.val[j]).val

  def split_invalid (nums : Slice Std.I64) (k : Nat) : Prop :=
    ∃ (i : Nat) (_hi : i < k) (j : Nat) (_ : k ≤ j) (_hj : j < nums.val.length),
      (nums.val[j]).val < (nums.val[i]).val

  /-- Let k be the integer value of r. Whenever the function returns a result r, k is the least integer with 1 <= k <= len(nums) such that for every i and j with 0 <= i < k and k <= j < len(nums), nums[i] <= nums[j]. For k = len(nums), the condition over j is vacuous.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        1 ≤ r.val.toNat ∧ r.val.toNat ≤ nums.val.length ∧
        split_valid nums r.val.toNat ∧
        (∀ (k : Nat) (_ : 1 ≤ k), k < r.val.toNat → ¬ split_valid nums k) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          1 ≤ r.val.toNat ∧ r.val.toNat ≤ nums.val.length ∧
          split_valid nums r.val.toNat ∧
          (∀ (k : Nat) (_ : 1 ≤ k), k < r.val.toNat → ¬ split_valid nums k)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r; it does not fail, panic, or overflow.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∃ r : Std.I64, partition_disjoint nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∃ r : Std.I64, partition_disjoint nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer value k of r satisfies 1 <= k <= len(nums).
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          1 ≤ r.val ∧ r.val ≤ (nums.val.length : Int)) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. The split after k elements is valid: for every i and j with 0 <= i < k and k <= j < len(nums), nums[i] <= nums[j]. When k = len(nums), there are no such j.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        split_valid nums r.val.toNat := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          split_valid nums r.val.toNat) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. For every h with 1 <= h < k, the split after h elements is invalid: there exist indices i and j with 0 <= i < h <= j < len(nums) and nums[i] > nums[j].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        ∀ (h : Nat) (_ : 1 ≤ h), h < r.val.toNat → split_invalid nums h := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          ∀ (h : Nat) (_ : 1 ≤ h), h < r.val.toNat → split_invalid nums h) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. For every h with 1 <= h <= len(nums) such that the split after h elements is valid (that is, for every i and j with 0 <= i < h and h <= j < len(nums), nums[i] <= nums[j]), we have k <= h.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        ∀ (h : Nat) (_ : 1 ≤ h) (_ : h ≤ nums.val.length), split_valid nums h →
          r.val.toNat ≤ h := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          ∀ (h : Nat) (_ : 1 ≤ h) (_ : h ≤ nums.val.length), split_valid nums h →
            r.val.toNat ≤ h) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. Then k = 1 if and only if for every j with 1 <= j < len(nums), nums[0] <= nums[j].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        (r.val.toNat = 1 ↔
          ∀ (j : Nat) (_ : 1 ≤ j) (_ : j < nums.val.length),
            (nums.val[0]).val ≤ (nums.val[j]).val) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          (r.val.toNat = 1 ↔
            ∀ (j : Nat) (_ : 1 ≤ j) (_ : j < nums.val.length),
              (nums.val[0]).val ≤ (nums.val[j]).val)) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. Then k = len(nums) if and only if for every h with 1 <= h < len(nums), the split after h elements is invalid: there exist indices i and j with 0 <= i < h <= j < len(nums) and nums[i] > nums[j].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        (r.val.toNat = nums.val.length ↔
          ∀ (h : Nat) (_ : 1 ≤ h) (_ : h < nums.val.length), split_invalid nums h) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          (r.val.toNat = nums.val.length ↔
            ∀ (h : Nat) (_ : 1 ≤ h) (_ : h < nums.val.length), split_invalid nums h)) := by
    sorry

  /-- Whenever the function returns a result r, the integer value k of r satisfies k <= len(nums) - 1.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Also assume for every i with 0 <= i < len(nums)-1, nums[i] <= nums[len(nums)-1]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
      (hlast : ∀ (i : Nat) (_ : i < nums.val.length - 1),
        (nums.val[i]).val ≤ (nums.val[nums.val.length - 1]).val) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        r.val ≤ (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
        (hlast : ∀ (i : Nat) (_ : i < nums.val.length - 1),
          (nums.val[i]).val ≤ (nums.val[nums.val.length - 1]).val), ∀ r : Std.I64, partition_disjoint nums = ok r →
          r.val ≤ (nums.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. There exists an index i with 0 <= i < k such that for every j with 0 <= j < len(nums), nums[i] <= nums[j].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        ∃ (i : Nat) (_hi : i < nums.val.length),
          i < r.val.toNat ∧
          ∀ (j : Nat) (_ : j < nums.val.length), (nums.val[i]).val ≤ (nums.val[j]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          ∃ (i : Nat) (_hi : i < nums.val.length),
            i < r.val.toNat ∧
            ∀ (j : Nat) (_ : j < nums.val.length), (nums.val[i]).val ≤ (nums.val[j]).val) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. If k < len(nums), then there exists an index j with k <= j < len(nums) such that for every i with 0 <= i < len(nums), nums[i] <= nums[j].
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        r.val.toNat < nums.val.length →
        ∃ (j : Nat) (_hj : j < nums.val.length),
          r.val.toNat ≤ j ∧
          ∀ (i : Nat) (_ : i < nums.val.length), (nums.val[i]).val ≤ (nums.val[j]).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          r.val.toNat < nums.val.length →
          ∃ (j : Nat) (_hj : j < nums.val.length),
            r.val.toNat ≤ j ∧
            ∀ (i : Nat) (_ : i < nums.val.length), (nums.val[i]).val ≤ (nums.val[j]).val) := by
    sorry

  /-- Whenever the function returns a result r, let k be its integer value. For every j with 0 <= j < len(nums), if nums[j] < nums[0], then j < k.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. -/
  theorem spec_12 (nums : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000) :
      ∀ r : Std.I64, partition_disjoint nums = ok r →
        ∀ (j : Nat) (_ : j < nums.val.length),
          (nums.val[j]).val < (nums.val[0]).val → j < r.val.toNat := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000), ∀ r : Std.I64, partition_disjoint nums = ok r →
          ∀ (j : Nat) (_ : j < nums.val.length),
            (nums.val[j]).val < (nums.val[0]).val → j < r.val.toNat) := by
    sorry

  /-- If partition_disjoint(nums) returns a result r and partition_disjoint(nums') returns a result r', then the integer values of r and r' are equal.
    Preconditions: Let n = len(nums). Assume 2 <= n <= 100000 and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000. Let nums' be any slice of length n satisfying 2 <= n <= 100000 and 0 <= nums'[i] <= 1000000 for every i with 0 <= i < n. Assume there is an integer c such that nums'[i] = nums[i] + c for every i with 0 <= i < n, with the addition performed within 64-bit range. -/
  theorem spec_13 (nums nums' : Slice Std.I64)
      (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
      (hval : ∀ (i : Nat) (_ : i < nums.val.length),
        0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
      (hlen'_eq : nums'.val.length = nums.val.length)
      (hlen'_lb : 2 ≤ nums'.val.length) (hlen'_ub : nums'.val.length ≤ 100000)
      (hval' : ∀ (i : Nat) (_ : i < nums'.val.length),
        0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000)
      (c : Int)
      (hshift : ∀ (i : Nat) (_ : i < nums.val.length),
        (nums'.val[i]).val = (nums.val[i]).val + c)
      (hrange : ∀ (i : Nat) (_ : i < nums.val.length),
        i64_min ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ i64_max) :
      ∀ r r' : Std.I64, partition_disjoint nums = ok r →
        partition_disjoint nums' = ok r' → r.val = r'.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums nums' : Slice Std.I64)
        (hlen_lb : 2 ≤ nums.val.length) (hlen_ub : nums.val.length ≤ 100000)
        (hval : ∀ (i : Nat) (_ : i < nums.val.length),
          0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000)
        (hlen'_eq : nums'.val.length = nums.val.length)
        (hlen'_lb : 2 ≤ nums'.val.length) (hlen'_ub : nums'.val.length ≤ 100000)
        (hval' : ∀ (i : Nat) (_ : i < nums'.val.length),
          0 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000)
        (c : Int)
        (hshift : ∀ (i : Nat) (_ : i < nums.val.length),
          (nums'.val[i]).val = (nums.val[i]).val + c)
        (hrange : ∀ (i : Nat) (_ : i < nums.val.length),
          i64_min ≤ (nums.val[i]).val + c ∧ (nums.val[i]).val + c ≤ i64_max), ∀ r r' : Std.I64, partition_disjoint nums = ok r →
          partition_disjoint nums' = ok r' → r.val = r'.val) := by
    sorry

  end AegisSpec.PartitionDisjoint
