import Aegis.MaximizeGreatness.Code.Funs

/-!
# Specifications of `Aegis.MaximizeGreatness.maximize_greatness`

LeetCode problem `maximize-greatness-of-an-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaximizeGreatness (maximize_greatness)

namespace AegisSpec.MaximizeGreatness

def countOcc (l : List Int) (v : Int) : Nat := (l.filter (fun x => x = v)).length

def IsRearrangement (nums perm : List Int) : Prop :=
  perm.length = nums.length ∧ ∀ v : Int, countOcc perm v = countOcc nums v

def maxMultiplicity (l : List Int) : Nat := (l.map (fun v => countOcc l v)).foldr max 0

def greatnessCount (nums perm : List Int) : Nat :=
  ((nums.zip perm).filter (fun p => p.2 > p.1)).length

def IsMaxGreatness (nums : List Int) (r : Int) : Prop :=
  (∀ perm : List Int, IsRearrangement nums perm → (greatnessCount nums perm : Int) ≤ r) ∧
    ∃ perm : List Int, IsRearrangement nums perm ∧ (greatnessCount nums perm : Int) = r

/-- The function returns a result r, and r equals the maximum, over all arrays perm of length len(nums) that are rearrangements of nums (that is, for every integer value v, the number of indices i with perm[i] = v equals the number of indices i with nums[i] = v), of the number of indices i with 0 <= i < len(nums) and perm[i] > nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : I64, maximize_greatness nums = ok r ∧ IsMaxGreatness nums.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : I64, maximize_greatness nums = ok r ∧ IsMaxGreatness nums.val r.val) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail with overflow, out-of-bounds access, or panic.
  Preconditions: 1 <= len(nums) <= 100000 and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : I64, maximize_greatness nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : I64, maximize_greatness nums = ok r) := by
  sorry

/-- Let m be the maximum, over all integer values v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r, r <= len(nums) - m.
  Preconditions: 1 <= len(nums) <= 100000 and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : I64, maximize_greatness nums = ok r →
      r.val ≤ (nums.val.length : Int) - (maxMultiplicity nums.val : Int) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : I64, maximize_greatness nums = ok r →
      r.val ≤ (nums.val.length : Int) - (maxMultiplicity nums.val : Int)) := by
  sorry

/-- Let m be the maximum, over all integer values v, of the number of indices i with 0 <= i < len(nums) and nums[i] = v. Whenever the function returns a result r, len(nums) - m <= r.
  Preconditions: 1 <= len(nums) <= 100000 and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : I64, maximize_greatness nums = ok r →
      (nums.val.length : Int) - (maxMultiplicity nums.val : Int) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : I64, maximize_greatness nums = ok r →
      (nums.val.length : Int) - (maxMultiplicity nums.val : Int) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, there exists an array perm of length len(nums) that is a rearrangement of nums and such that exactly r indices i with 0 <= i < len(nums) satisfy perm[i] > nums[i].
  Preconditions: 1 <= len(nums) <= 100000 and for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : I64, maximize_greatness nums = ok r →
      ∃ perm : List Int, IsRearrangement nums.val perm ∧
        (greatnessCount nums.val perm : Int) = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : I64, maximize_greatness nums = ok r →
      ∃ perm : List Int, IsRearrangement nums.val perm ∧
        (greatnessCount nums.val perm : Int) = r.val) := by
  sorry

/-- If the function returns r on nums and returns r2 on nums2, then r = r2.
  Preconditions: 1 <= len(nums) <= 100000; for every index i with 0 <= i < len(nums), 0 <= nums[i] <= 1000000000; nums2 is an array of the same length such that for every integer value v, the number of indices i with nums2[i] = v equals the number of indices i with nums[i] = v. -/
theorem spec_6 (nums nums2 : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (h_len2 : nums2.val.length = nums.val.length)
    (h_counts : ∀ v : Int, countOcc nums2.val v = countOcc nums.val v) :
    ∀ r r2 : I64, maximize_greatness nums = ok r → maximize_greatness nums2 = ok r2 →
      r = r2 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums nums2 : Slice I64)
    (h_len_lower : 1 ≤ nums.val.length) (h_len_upper : nums.val.length ≤ 100000)
    (h_entries : ∀ (i : Nat) (hi : i < nums.val.length),
      0 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (h_len2 : nums2.val.length = nums.val.length)
    (h_counts : ∀ v : Int, countOcc nums2.val v = countOcc nums.val v), ∀ r r2 : I64, maximize_greatness nums = ok r → maximize_greatness nums2 = ok r2 →
      r = r2) := by
  sorry

end AegisSpec.MaximizeGreatness
