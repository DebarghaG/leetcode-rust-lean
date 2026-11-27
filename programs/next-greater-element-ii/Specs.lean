import Aegis.NextGreaterElements.Code.Funs

/-!
# Specifications of `Aegis.NextGreaterElements.next_greater_elements`

LeetCode problem `next-greater-element-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NextGreaterElements

  open Aegis.NextGreaterElements

  def getI (l : List Std.I64) (i : Nat) : Int :=
    (l.getD i 0#i64).val

  def maxI (l : List Std.I64) : Nat → Int
    | 0 => getI l 0
    | k + 1 => max (maxI l k) (getI l k)

  /-- The function returns a vector r such that len(r) = n and for every i with 0 <= i < n: if there is no d with 1 <= d < n and nums[(i+d) mod n] > nums[i], then r[i] = -1; otherwise, for the least such d, r[i] = nums[(i+d) mod n].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r ∧ r.val.length = n ∧
          ∀ i, i < n →
            ((∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i) →
                getI r.val i = -1) ∧
              (∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) > getI nums.val i →
                (∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i) →
                  getI r.val i = getI nums.val ((i + d) % n)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r ∧ r.val.length = n ∧
            ∀ i, i < n →
              ((∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i) →
                  getI r.val i = -1) ∧
                (∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) > getI nums.val i →
                  (∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i) →
                    getI r.val i = getI nums.val ((i + d) % n))) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, or panic).
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∃ r : alloc.vec.Vec Std.I64, next_greater_elements nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64, next_greater_elements nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = len(nums).
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r → r.val.length = nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r → r.val.length = nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, either r[i] = -1 or r[i] > nums[i].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i = -1 ∨ getI r.val i > getI nums.val i := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i = -1 ∨ getI r.val i > getI nums.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then there exists j with 0 <= j < n such that j != i and nums[j] = r[i].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i ≠ -1 →
            ∃ j, j < n ∧ j ≠ i ∧ getI nums.val j = getI r.val i := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i ≠ -1 →
              ∃ j, j < n ∧ j ≠ i ∧ getI nums.val j = getI r.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then there exists d with 1 <= d < n such that r[i] = nums[(i+d) mod n] > nums[i], and for every e with 1 <= e < d, nums[(i+e) mod n] <= nums[i].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i ≠ -1 →
            ∃ d, 1 ≤ d ∧ d < n ∧ getI r.val i = getI nums.val ((i + d) % n) ∧
              getI nums.val ((i + d) % n) > getI nums.val i ∧
                ∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i ≠ -1 →
              ∃ d, 1 ≤ d ∧ d < n ∧ getI r.val i = getI nums.val ((i + d) % n) ∧
                getI nums.val ((i + d) % n) > getI nums.val i ∧
                  ∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = -1 and there exists d with 1 <= d < n such that nums[(i+d) mod n] > nums[i], then for the least such d we have nums[(i+d) mod n] = -1.
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i = -1 →
            (∃ d, 1 ≤ d ∧ d < n ∧ getI nums.val ((i + d) % n) > getI nums.val i) →
              ∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) > getI nums.val i →
                (∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i) →
                  getI nums.val ((i + d) % n) = -1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i = -1 →
              (∃ d, 1 ≤ d ∧ d < n ∧ getI nums.val ((i + d) % n) > getI nums.val i) →
                ∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) > getI nums.val i →
                  (∀ e, 1 ≤ e → e < d → getI nums.val ((i + e) % n) ≤ getI nums.val i) →
                    getI nums.val ((i + d) % n) = -1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if for every d with 1 <= d < n, nums[(i+d) mod n] <= nums[i], then r[i] = -1.
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n →
            (∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i) →
              getI r.val i = -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n →
              (∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i) →
                getI r.val i = -1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if nums[i] >= nums[j] for every j with 0 <= j < n, then r[i] = -1.
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_9 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n →
            (∀ j, j < n → getI nums.val j ≤ getI nums.val i) → getI r.val i = -1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n →
              (∀ j, j < n → getI nums.val j ≤ getI nums.val i) → getI r.val i = -1) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if nums[i] < nums[(i+1) mod n], then r[i] = nums[(i+1) mod n].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_10 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n →
            getI nums.val i < getI nums.val ((i + 1) % n) →
              getI r.val i = getI nums.val ((i + 1) % n) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n →
              getI nums.val i < getI nums.val ((i + 1) % n) →
                getI r.val i = getI nums.val ((i + 1) % n)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, either r[i] = -1 or -1000000000 <= r[i] <= 1000000000.
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_11 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n →
            getI r.val i = -1 ∨
              (-1000000000 ≤ getI r.val i ∧ getI r.val i ≤ 1000000000) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n →
              getI r.val i = -1 ∨
                (-1000000000 ≤ getI r.val i ∧ getI r.val i ≤ 1000000000)) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] != -1 then r[i] <= max{nums[j] | 0 <= j < n}.
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_12 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i ≠ -1 → getI r.val i ≤ maxI nums.val n := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i ≠ -1 → getI r.val i ≤ maxI nums.val n) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < n, if r[i] = -1 and nums[i] >= -1, then for every d with 1 <= d < n, nums[(i+d) mod n] <= nums[i].
    Preconditions: nums is a slice of i64 with n = len(nums), 1 <= n <= 10000, and for every j with 0 <= j < n, -1000000000 <= nums[j] <= 1000000000. -/
  theorem spec_13 (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
      (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
      (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000) :
      ∀ r : alloc.vec.Vec Std.I64,
        next_greater_elements nums = ok r →
          ∀ i, i < n → getI r.val i = -1 → -1 ≤ getI nums.val i →
            ∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (nums : Slice Std.I64) (n : Nat) (hn : n = nums.val.length)
        (hn_pos : 1 ≤ n) (hn_le : n ≤ 10000)
        (hb : ∀ j, j < n → -1000000000 ≤ getI nums.val j ∧ getI nums.val j ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
          next_greater_elements nums = ok r →
            ∀ i, i < n → getI r.val i = -1 → -1 ≤ getI nums.val i →
              ∀ d, 1 ≤ d → d < n → getI nums.val ((i + d) % n) ≤ getI nums.val i) := by
    sorry

  end AegisSpec.NextGreaterElements
