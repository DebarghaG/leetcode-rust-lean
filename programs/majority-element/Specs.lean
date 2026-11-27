import Aegis.MajorityElement.Code.Funs

/-!
# Specifications of `Aegis.MajorityElement.majority_element`

LeetCode problem `majority-element`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MajorityElement

def freq (l : List Std.I64) (v : Std.I64) : ℕ :=
  (l.filter fun x => decide (x.val = v.val)).length

/-- Whenever majority_element(nums) returns a result r, r is the majority element of nums: 2 * freq(r) > n.
  Preconditions: Let n = len(nums). For a value v, let freq(v) be the number of indices i with 0 <= i < n and nums[i] = v. Assume 1 <= n <= 50000, every nums[i] with 0 <= i < n lies in [-10^9, 10^9], and there exists a value v with 2 * freq(v) > n (the majority-existence guarantee). -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hbounds : ∀ x ∈ nums.val, (-1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hmaj : ∃ v : Std.I64, 2 * freq nums.val v > nums.val.length) :
    ∀ r : Std.I64, Aegis.MajorityElement.majority_element nums = ok r →
      2 * freq nums.val r > nums.val.length := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hbounds : ∀ x ∈ nums.val, (-1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hmaj : ∃ v : Std.I64, 2 * freq nums.val v > nums.val.length), ∀ r : Std.I64, Aegis.MajorityElement.majority_element nums = ok r →
      2 * freq nums.val r > nums.val.length) := by
  sorry

/-- For every input satisfying the preconditions, majority_element(nums) returns a result r; it does not fail (no panic, out-of-bounds access, or arithmetic overflow).
  Preconditions: Let n = len(nums). Assume 1 <= n <= 50000, every nums[i] with 0 <= i < n lies in [-10^9, 10^9], and nums has a majority element, i.e. some value occurs more than floor(n/2) times in nums. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hbounds : ∀ x ∈ nums.val, (-1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hmaj : ∃ v : Std.I64, freq nums.val v > nums.val.length / 2) :
    ∃ r : Std.I64, Aegis.MajorityElement.majority_element nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_pos : 1 ≤ nums.val.length)
    (hlen_le : nums.val.length ≤ 50000)
    (hbounds : ∀ x ∈ nums.val, (-1000000000 : ℤ) ≤ x.val ∧ x.val ≤ 1000000000)
    (hmaj : ∃ v : Std.I64, freq nums.val v > nums.val.length / 2), ∃ r : Std.I64, Aegis.MajorityElement.majority_element nums = ok r) := by
  sorry

end AegisSpec.MajorityElement
