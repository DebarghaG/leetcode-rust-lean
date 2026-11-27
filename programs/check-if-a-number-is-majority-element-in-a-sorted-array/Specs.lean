import Aegis.IsMajorityElement.Code.Funs

/-!
# Specifications of `Aegis.IsMajorityElement.is_majority_element`

LeetCode problem `check-if-a-number-is-majority-element-in-a-sorted-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsMajorityElement

  def elems (nums : Slice Std.I64) : List ℤ := nums.val.map (fun x => x.val)

  def SortedUp (nums : Slice Std.I64) : Prop :=
    ∀ (i j : ℕ) (a b : ℤ), i ≤ j → (elems nums)[i]? = some a → (elems nums)[j]? = some b → a ≤ b

  def ElemsInRange (nums : Slice Std.I64) : Prop :=
    ∀ (i : ℕ) (a : ℤ), (elems nums)[i]? = some a → 1 ≤ a ∧ a ≤ 10 ^ 9

  def Occurs (nums : Slice Std.I64) (t : ℤ) : Prop :=
    ∃ i : ℕ, (elems nums)[i]? = some t

  def occCount (nums : Slice Std.I64) (t : ℤ) : ℕ :=
    (elems nums).countP (fun v => decide (v = t))

  def countBelow (nums : Slice Std.I64) (t : ℤ) : ℕ :=
    (elems nums).countP (fun v => decide (v < t))

  def countAbove (nums : Slice Std.I64) (t : ℤ) : ℕ :=
    (elems nums).countP (fun v => decide (t < v))

  def firstOcc? (nums : Slice Std.I64) (t : ℤ) : Option ℕ :=
    (List.range (elems nums).length).find? (fun i => decide ((elems nums)[i]? = some t))

  def lastOcc? (nums : Slice Std.I64) (t : ℤ) : Option ℕ :=
    (List.range (elems nums).length).reverse.find?
      (fun i => decide ((elems nums)[i]? = some t))

  /-- The function returns a result r (it does not fail) and r = true if and only if 2 * cnt > len(nums), where cnt is the number of indices i with 0 <= i < len(nums) such that nums[i] = target.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order (for all i, j with 0 <= i <= j < len(nums), nums[i] <= nums[j]); for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_1 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∃ r : Bool,
        Aegis.IsMajorityElement.is_majority_element nums target = ok r ∧
          (r = true ↔ 2 * occCount nums target.val > (elems nums).length) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∃ r : Bool,
          Aegis.IsMajorityElement.is_majority_element nums target = ok r ∧
            (r = true ↔ 2 * occCount nums target.val > (elems nums).length)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then nums[len(nums)/2] = target, where len(nums)/2 denotes integer division (floor).
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_2 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
        (elems nums)[(elems nums).length / 2]? = some target.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
          (elems nums)[(elems nums).length / 2]? = some target.val) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then there exists an index i with 0 <= i < len(nums) such that nums[i] = target.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_3 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
        Occurs nums target.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
          Occurs nums target.val) := by
    sorry

  /-- For any two inputs (nums1, target) and (nums2, target) satisfying the preconditions, if len(nums1) = len(nums2) and the number of occurrences of target in nums1 equals the number of occurrences of target in nums2, then whenever the function returns results r1 for the first input and r2 for the second, r1 = r2.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64) (target : Std.I64)
      (hlen1_pos : 1 ≤ (elems nums1).length) (hlen1_le : (elems nums1).length ≤ 1000)
      (hsorted1 : SortedUp nums1) (hrange1 : ElemsInRange nums1)
      (hlen2_pos : 1 ≤ (elems nums2).length) (hlen2_le : (elems nums2).length ≤ 1000)
      (hsorted2 : SortedUp nums2) (hrange2 : ElemsInRange nums2)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9)
      (hlen_eq : (elems nums1).length = (elems nums2).length)
      (hcount_eq : occCount nums1 target.val = occCount nums2 target.val) :
      ∀ r1 r2 : Bool,
        Aegis.IsMajorityElement.is_majority_element nums1 target = ok r1 →
          Aegis.IsMajorityElement.is_majority_element nums2 target = ok r2 → r1 = r2 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (target : Std.I64)
        (hlen1_pos : 1 ≤ (elems nums1).length) (hlen1_le : (elems nums1).length ≤ 1000)
        (hsorted1 : SortedUp nums1) (hrange1 : ElemsInRange nums1)
        (hlen2_pos : 1 ≤ (elems nums2).length) (hlen2_le : (elems nums2).length ≤ 1000)
        (hsorted2 : SortedUp nums2) (hrange2 : ElemsInRange nums2)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9)
        (hlen_eq : (elems nums1).length = (elems nums2).length)
        (hcount_eq : occCount nums1 target.val = occCount nums2 target.val), ∀ r1 r2 : Bool,
          Aegis.IsMajorityElement.is_majority_element nums1 target = ok r1 →
            Aegis.IsMajorityElement.is_majority_element nums2 target = ok r2 → r1 = r2) := by
    sorry

  /-- For any two inputs (nums1, target) and (nums2, target) satisfying the preconditions with len(nums1) = len(nums2), if the number of occurrences of target in nums1 is less than or equal to the number of occurrences of target in nums2, then whenever the function returns r1 for the first and r2 for the second, r1 = true implies r2 = true.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (target : Std.I64)
      (hlen1_pos : 1 ≤ (elems nums1).length) (hlen1_le : (elems nums1).length ≤ 1000)
      (hsorted1 : SortedUp nums1) (hrange1 : ElemsInRange nums1)
      (hlen2_pos : 1 ≤ (elems nums2).length) (hlen2_le : (elems nums2).length ≤ 1000)
      (hsorted2 : SortedUp nums2) (hrange2 : ElemsInRange nums2)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9)
      (hlen_eq : (elems nums1).length = (elems nums2).length)
      (hcount_le : occCount nums1 target.val ≤ occCount nums2 target.val) :
      ∀ r1 r2 : Bool,
        Aegis.IsMajorityElement.is_majority_element nums1 target = ok r1 →
          Aegis.IsMajorityElement.is_majority_element nums2 target = ok r2 → r1 = true →
            r2 = true := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (target : Std.I64)
        (hlen1_pos : 1 ≤ (elems nums1).length) (hlen1_le : (elems nums1).length ≤ 1000)
        (hsorted1 : SortedUp nums1) (hrange1 : ElemsInRange nums1)
        (hlen2_pos : 1 ≤ (elems nums2).length) (hlen2_le : (elems nums2).length ≤ 1000)
        (hsorted2 : SortedUp nums2) (hrange2 : ElemsInRange nums2)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9)
        (hlen_eq : (elems nums1).length = (elems nums2).length)
        (hcount_le : occCount nums1 target.val ≤ occCount nums2 target.val), ∀ r1 r2 : Bool,
          Aegis.IsMajorityElement.is_majority_element nums1 target = ok r1 →
            Aegis.IsMajorityElement.is_majority_element nums2 target = ok r2 → r1 = true →
              r2 = true) := by
    sorry

  /-- Whenever the function returns a result r, if target occurs in nums, let f be the smallest index with 0 <= f < len(nums) and nums[f] = target, and let l be the largest index with 0 <= l < len(nums) and nums[l] = target. Then r = true if and only if 2 * (l - f + 1) > len(nums). If target does not occur in nums, then r = false.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_6 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r →
        (∀ (lo hi : ℕ), firstOcc? nums target.val = some lo →
            lastOcc? nums target.val = some hi →
              (r = true ↔ 2 * (hi - lo + 1) > (elems nums).length)) ∧
          (¬ Occurs nums target.val → r = false) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r →
          (∀ (lo hi : ℕ), firstOcc? nums target.val = some lo →
              lastOcc? nums target.val = some hi →
                (r = true ↔ 2 * (hi - lo + 1) > (elems nums).length)) ∧
            (¬ Occurs nums target.val → r = false)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then for every value v with v != target, the number of occurrences of v in nums is strictly less than the number of occurrences of target in nums.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_7 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
        ∀ v : ℤ, v ≠ target.val → occCount nums v < occCount nums target.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
          ∀ v : ℤ, v ≠ target.val → occCount nums v < occCount nums target.val) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then if f is the smallest index with 0 <= f < len(nums) and nums[f] = target, and l is the largest index with 0 <= l < len(nums) and nums[l] = target, we have f <= len(nums)/2 <= l, where len(nums)/2 denotes integer division (floor).
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_8 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
        ∀ (lo hi : ℕ), firstOcc? nums target.val = some lo →
          lastOcc? nums target.val = some hi →
            lo ≤ (elems nums).length / 2 ∧ (elems nums).length / 2 ≤ hi := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
          ∀ (lo hi : ℕ), firstOcc? nums target.val = some lo →
            lastOcc? nums target.val = some hi →
              lo ≤ (elems nums).length / 2 ∧ (elems nums).length / 2 ≤ hi) := by
    sorry

  /-- For any nums satisfying the preconditions, and any two distinct values target1 and target2 in [1, 10^9], whenever the function returns r1 for (nums, target1) and r2 for (nums, target2), if r1 = true then r2 = false.
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target1, target2 <= 10^9; target1 != target2. -/
  theorem spec_9 (nums : Slice Std.I64) (target1 target2 : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget1_pos : 1 ≤ target1.val) (htarget1_le : target1.val ≤ 10 ^ 9)
      (htarget2_pos : 1 ≤ target2.val) (htarget2_le : target2.val ≤ 10 ^ 9)
      (hne : target1.val ≠ target2.val) :
      ∀ r1 r2 : Bool,
        Aegis.IsMajorityElement.is_majority_element nums target1 = ok r1 →
          Aegis.IsMajorityElement.is_majority_element nums target2 = ok r2 → r1 = true →
            r2 = false := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (target1 target2 : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget1_pos : 1 ≤ target1.val) (htarget1_le : target1.val ≤ 10 ^ 9)
        (htarget2_pos : 1 ≤ target2.val) (htarget2_le : target2.val ≤ 10 ^ 9)
        (hne : target1.val ≠ target2.val), ∀ r1 r2 : Bool,
          Aegis.IsMajorityElement.is_majority_element nums target1 = ok r1 →
            Aegis.IsMajorityElement.is_majority_element nums target2 = ok r2 → r1 = true →
              r2 = false) := by
    sorry

  /-- Whenever the function returns a result r, if r = true, then the number of indices i with 0 <= i < len(nums) and nums[i] < target is strictly less than len(nums)/2, and the number of indices i with 0 <= i < len(nums) and nums[i] > target is strictly less than len(nums)/2. Equivalently, twice each of these counts is strictly less than len(nums).
    Preconditions: 1 <= len(nums) <= 1000; nums is sorted in non-decreasing order; for all i with 0 <= i < len(nums), 1 <= nums[i] <= 10^9; 1 <= target <= 10^9. -/
  theorem spec_10 (nums : Slice Std.I64) (target : Std.I64)
      (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
      (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
      (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9) :
      ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
        2 * countBelow nums target.val < (elems nums).length ∧
          2 * countAbove nums target.val < (elems nums).length := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (target : Std.I64)
        (hlen_pos : 1 ≤ (elems nums).length) (hlen_le : (elems nums).length ≤ 1000)
        (hsorted : SortedUp nums) (hrange : ElemsInRange nums)
        (htarget_pos : 1 ≤ target.val) (htarget_le : target.val ≤ 10 ^ 9), ∀ r : Bool, Aegis.IsMajorityElement.is_majority_element nums target = ok r → r = true →
          2 * countBelow nums target.val < (elems nums).length ∧
            2 * countAbove nums target.val < (elems nums).length) := by
    sorry

  theorem elems_length (nums : Slice Std.I64) : (elems nums).length = Slice.length nums := by
    simp [elems]

  end AegisSpec.IsMajorityElement
