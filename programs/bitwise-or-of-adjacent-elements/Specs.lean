import Aegis.OrArray.Code.Funs

/-!
# Specifications of `Aegis.OrArray.or_array`

LeetCode problem `bitwise-or-of-adjacent-elements`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.OrArray

namespace AegisSpec.OrArray

/-- The function returns a result r and len(r) = len(nums) - 1; moreover, for every i with 0 <= i < len(nums) - 1, r[i] = nums[i] | nums[i+1], where | is bitwise OR on 64-bit integers.
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_1 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ (r : alloc.vec.Vec I64) (_hok : or_array nums = ok r)
      (hlen : r.val.length = nums.val.length - 1),
      ∀ (i : Nat) (hi : i < nums.val.length - 1),
        (r.val[i]).val = (nums.val[i] ||| nums.val[i + 1]).val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ (r : alloc.vec.Vec I64) (_hok : or_array nums = ok r)
      (hlen : r.val.length = nums.val.length - 1),
      ∀ (i : Nat) (hi : i < nums.val.length - 1),
        (r.val[i]).val = (nums.val[i] ||| nums.val[i + 1]).val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, len(r) = len(nums) - 1.
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_2 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      r.val.length = nums.val.length - 1 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      r.val.length = nums.val.length - 1) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, 0 <= r[i] <= 127.
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_3 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        0 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 127 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        0 ≤ (r.val[i]).val ∧ (r.val[i]).val ≤ 127) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, r[i] >= nums[i] and r[i] >= nums[i+1].
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_4 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val ≤ (r.val[i]).val ∧ (nums.val[i + 1]).val ≤ (r.val[i]).val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val ≤ (r.val[i]).val ∧ (nums.val[i + 1]).val ≤ (r.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, r[i] <= nums[i] + nums[i+1].
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_5 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (r.val[i]).val ≤ (nums.val[i]).val + (nums.val[i + 1]).val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (r.val[i]).val ≤ (nums.val[i]).val + (nums.val[i + 1]).val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, if nums[i] = 0 then r[i] = nums[i+1].
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_6 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val = 0 → (r.val[i]).val = (nums.val[i + 1]).val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val = 0 → (r.val[i]).val = (nums.val[i + 1]).val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, if nums[i+1] = 0 then r[i] = nums[i].
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_7 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i + 1]).val = 0 → (r.val[i]).val = (nums.val[i]).val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i + 1]).val = 0 → (r.val[i]).val = (nums.val[i]).val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, for every i with 0 <= i < len(nums) - 1, if nums[i] = nums[i+1] then r[i] = nums[i].
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_8 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val = (nums.val[i + 1]).val →
          (r.val[i]).val = (nums.val[i]).val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∀ (r : alloc.vec.Vec I64), or_array nums = ok r →
      ∀ (_hlen : r.val.length = nums.val.length - 1)
        (i : Nat) (hi : i < nums.val.length - 1),
        (nums.val[i]).val = (nums.val[i + 1]).val →
          (r.val[i]).val = (nums.val[i]).val) := by
  sorry

/-- Let n = len(a) = len(b), and let i be any index with 0 <= i < n - 1. If a[i] = b[i] and a[i+1] = b[i+1], then whenever or_array(a) returns r_a and or_array(b) returns r_b, r_a[i] = r_b[i].
  Preconditions: For two slices a and b, both satisfy 2 <= len(a) = len(b) <= 100, and every entry of a and every entry of b lies in [0, 100]. -/
theorem spec_9 (a b : Slice I64)
    (hmin : 2 ≤ a.val.length)
    (hlen : a.val.length = b.val.length)
    (hmax : a.val.length ≤ 100)
    (hrange_a : ∀ (i : Nat) (hi : i < a.val.length),
      0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 100)
    (hrange_b : ∀ (i : Nat) (hi : i < b.val.length),
      0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 100) :
    ∀ (i : Nat) (hi : i < a.val.length - 1),
      (a.val[i]).val = (b.val[i]).val →
      (a.val[i + 1]).val = (b.val[i + 1]).val →
      ∀ (ra rb : alloc.vec.Vec I64),
        or_array a = ok ra → or_array b = ok rb →
        (_hlen_a : ra.val.length = a.val.length - 1) →
        (_hlen_b : rb.val.length = b.val.length - 1) →
        (ra.val[i]).val = (rb.val[i]).val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (a b : Slice I64)
    (hmin : 2 ≤ a.val.length)
    (hlen : a.val.length = b.val.length)
    (hmax : a.val.length ≤ 100)
    (hrange_a : ∀ (i : Nat) (hi : i < a.val.length),
      0 ≤ (a.val[i]).val ∧ (a.val[i]).val ≤ 100)
    (hrange_b : ∀ (i : Nat) (hi : i < b.val.length),
      0 ≤ (b.val[i]).val ∧ (b.val[i]).val ≤ 100), ∀ (i : Nat) (hi : i < a.val.length - 1),
      (a.val[i]).val = (b.val[i]).val →
      (a.val[i + 1]).val = (b.val[i + 1]).val →
      ∀ (ra rb : alloc.vec.Vec I64),
        or_array a = ok ra → or_array b = ok rb →
        (_hlen_a : ra.val.length = a.val.length - 1) →
        (_hlen_b : rb.val.length = b.val.length - 1) →
        (ra.val[i]).val = (rb.val[i]).val) := by
  sorry

/-- The function returns a result r (it does not fail) for every slice nums satisfying the precondition.
  Preconditions: 2 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 100. -/
theorem spec_10 (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100) :
    ∃ r : alloc.vec.Vec I64, or_array nums = ok r := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64)
    (hmin : 2 ≤ nums.val.length)
    (hmax : nums.val.length ≤ 100)
    (hrange : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100), ∃ r : alloc.vec.Vec I64, or_array nums = ok r) := by
  sorry

end AegisSpec.OrArray
