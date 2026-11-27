import Aegis.MajorityElement.Code.Funs

/-!
# Specifications of `Aegis.MajorityElement.majority_element`

LeetCode problem `majority-element-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MajorityElement

def countOcc (l : List Std.I64) (x : Std.I64) : ℕ :=
  l.countP (fun y => decide (y = x))

def threshold (l : List Std.I64) : ℕ :=
  l.length / 3

def majorityValues (l : List Std.I64) : Finset Std.I64 :=
  l.toFinset.filter (fun x => countOcc l x > threshold l)

def PairwiseDistinct (l : List Std.I64) : Prop :=
  ∀ (j : ℕ) (hj : j < l.length) (k : ℕ) (hk : k < l.length), l[j]'hj = l[k]'hk → j = k

def SameMultiplicities (l l' : List Std.I64) : Prop :=
  ∀ x : Std.I64, countOcc l x = countOcc l' x

/-- The function returns a result r and, for every 64-bit integer x, the number of indices j with 0 <= j < len(r) and r[j] = x is 1 if the number of indices i with 0 <= i < len(nums) and nums[i] = x is greater than len(nums)/3, and is 0 otherwise.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_1 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r ∧
        ∀ x : Std.I64,
          countOcc r.val x = if countOcc nums.val x > threshold nums.val then 1 else 0 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r ∧
        ∀ x : Std.I64,
          countOcc r.val x = if countOcc nums.val x > threshold nums.val then 1 else 0) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow on any input satisfying the preconditions.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_2 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r) := by
  sorry

/-- Whenever the function returns a result r, all positions of r contain pairwise distinct values: for every j and k with 0 <= j < len(r) and 0 <= k < len(r), if r[j] = r[k], then j = k.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_3 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r → PairwiseDistinct r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r → PairwiseDistinct r.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= 2.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_4 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r → r.val.length ≤ 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r → r.val.length ≤ 2) := by
  sorry

/-- Whenever the function returns a result r, len(r) equals the number of distinct 64-bit integers x such that the number of indices i with 0 <= i < len(nums) and nums[i] = x is greater than len(nums)/3.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_5 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        r.val.length = (majorityValues nums.val).card := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        r.val.length = (majorityValues nums.val).card) := by
  sorry

/-- Whenever the function returns a result r, for every 64-bit integer x, if the number of indices i with 0 <= i < len(nums) and nums[i] = x is greater than len(nums)/3, then there exists an index j with 0 <= j < len(r) and r[j] = x.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_6 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        ∀ x : Std.I64,
          countOcc nums.val x > threshold nums.val →
            ∃ (j : ℕ) (hj : j < r.val.length), r.val[j]'hj = x := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        ∀ x : Std.I64,
          countOcc nums.val x > threshold nums.val →
            ∃ (j : ℕ) (hj : j < r.val.length), r.val[j]'hj = x) := by
  sorry

/-- Whenever the function returns a result r, for every index j with 0 <= j < len(r), the number of indices i with 0 <= i < len(nums) and nums[i] = r[j] is greater than len(nums)/3.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_7 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length),
          countOcc nums.val (r.val[j]'hj) > threshold nums.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        ∀ (j : ℕ) (hj : j < r.val.length),
          countOcc nums.val (r.val[j]'hj) > threshold nums.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) = 0 if and only if for every 64-bit integer x, the number of indices i with 0 <= i < len(nums) and nums[i] = x is at most len(nums)/3.
  Preconditions: 1 <= len(nums) <= 50000 and for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000. -/
theorem spec_8 (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        (r.val.length = 0 ↔ ∀ x : Std.I64, countOcc nums.val x ≤ threshold nums.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MajorityElement.majority_element nums = ok r →
        (r.val.length = 0 ↔ ∀ x : Std.I64, countOcc nums.val x ≤ threshold nums.val)) := by
  sorry

/-- Whenever the function returns a result r for nums and a result r' for nums', the results have the same multiset of values: for every 64-bit integer x, the number of indices j with 0 <= j < len(r) and r[j] = x equals the number of indices j with 0 <= j < len(r') and r'[j] = x.
  Preconditions: 1 <= len(nums) <= 50000, 1 <= len(nums') <= 50000, for every i with 0 <= i < len(nums), -1000000000 <= nums[i] <= 1000000000, for every i with 0 <= i < len(nums'), -1000000000 <= nums'[i] <= 1000000000, and nums' is a permutation of nums in the sense that for every 64-bit integer x, the number of indices i with 0 <= i < len(nums) and nums[i] = x equals the number of indices i with 0 <= i < len(nums') and nums'[i] = x. -/
theorem spec_9 (nums nums' : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen_lower' : 1 ≤ nums'.val.length)
    (hlen_upper' : nums'.val.length ≤ 50000)
    (hbounds' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -1000000000 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
    (hperm : SameMultiplicities nums.val nums'.val) :
    ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.MajorityElement.majority_element nums = ok r →
        Aegis.MajorityElement.majority_element nums' = ok r' →
          SameMultiplicities r.val r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums nums' : Slice Std.I64)
    (hlen_lower : 1 ≤ nums.val.length)
    (hlen_upper : nums.val.length ≤ 50000)
    (hbounds : ∀ (i : ℕ) (hi : i < nums.val.length),
      -1000000000 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000000000)
    (hlen_lower' : 1 ≤ nums'.val.length)
    (hlen_upper' : nums'.val.length ≤ 50000)
    (hbounds' : ∀ (i : ℕ) (hi : i < nums'.val.length),
      -1000000000 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000000000)
    (hperm : SameMultiplicities nums.val nums'.val), ∀ (r r' : alloc.vec.Vec Std.I64),
      Aegis.MajorityElement.majority_element nums = ok r →
        Aegis.MajorityElement.majority_element nums' = ok r' →
          SameMultiplicities r.val r'.val) := by
  sorry

end AegisSpec.MajorityElement
