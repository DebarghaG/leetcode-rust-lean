import Aegis.BeautifulPair.Code.Funs

/-!
# Specifications of `Aegis.BeautifulPair.beautiful_pair`

LeetCode problem `beautiful-pairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.BeautifulPair

  def coord (s : Slice Std.I64) (i : ℤ) : ℤ :=
    (s.val.getD i.toNat (0#i64)).val

  def dist (nums1 nums2 : Slice Std.I64) (a b : ℤ) : ℕ :=
    (coord nums1 a - coord nums1 b).natAbs + (coord nums2 a - coord nums2 b).natAbs

  def AllValuesInRange (s : Slice Std.I64) : Prop :=
    ∀ (i : ℕ) (hi : i < s.val.length),
      0 ≤ (s.val[i]'hi).val ∧ (s.val[i]'hi).val ≤ 100000

  /-- Whenever beautiful_pair(nums1, nums2) returns a result r, define d(a,b) = abs(nums1[a] - nums1[b]) + abs(nums2[a] - nums2[b]) for indices a,b. Then len(r) = 2, 0 <= r[0] < r[1] < n, and for every pair of indices (i,j) with 0 <= i < j < n, d(r[0],r[1]) <= d(i,j). Moreover, for every pair (i,j) with 0 <= i < j < n and d(i,j) = d(r[0],r[1]), the pair (r[0],r[1]) is lexicographically no greater than (i,j), meaning r[0] < i or (r[0] = i and r[1] <= j).
    Preconditions: Let n = len(nums1). The arrays satisfy len(nums2) = n, 2 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100000 and 0 <= nums2[i] <= 100000. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (hlen : nums2.length = nums1.length)
      (hmin : 2 ≤ nums1.length)
      (hmax : nums1.length ≤ 100000)
      (hbound1 : AllValuesInRange nums1)
      (hbound2 : AllValuesInRange nums2) :
      ∀ (r : alloc.vec.Vec Std.I64), Aegis.BeautifulPair.beautiful_pair nums1 nums2 = ok r →
        r.val.length = 2 ∧
        ∃ (a b : ℤ),
          r.val.map (fun x => x.val) = [a, b] ∧
          0 ≤ a ∧ a < b ∧ b < (nums1.length : ℤ) ∧
          (∀ (i j : ℤ), 0 ≤ i → i < j → j < (nums1.length : ℤ) →
            dist nums1 nums2 a b ≤ dist nums1 nums2 i j) ∧
          (∀ (i j : ℤ), 0 ≤ i → i < j → j < (nums1.length : ℤ) →
            dist nums1 nums2 i j = dist nums1 nums2 a b →
              a < i ∨ (a = i ∧ b ≤ j)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen : nums2.length = nums1.length)
        (hmin : 2 ≤ nums1.length)
        (hmax : nums1.length ≤ 100000)
        (hbound1 : AllValuesInRange nums1)
        (hbound2 : AllValuesInRange nums2), ∀ (r : alloc.vec.Vec Std.I64), Aegis.BeautifulPair.beautiful_pair nums1 nums2 = ok r →
          r.val.length = 2 ∧
          ∃ (a b : ℤ),
            r.val.map (fun x => x.val) = [a, b] ∧
            0 ≤ a ∧ a < b ∧ b < (nums1.length : ℤ) ∧
            (∀ (i j : ℤ), 0 ≤ i → i < j → j < (nums1.length : ℤ) →
              dist nums1 nums2 a b ≤ dist nums1 nums2 i j) ∧
            (∀ (i j : ℤ), 0 ≤ i → i < j → j < (nums1.length : ℤ) →
              dist nums1 nums2 i j = dist nums1 nums2 a b →
                a < i ∨ (a = i ∧ b ≤ j))) := by
    sorry

  /-- On every input satisfying the preconditions, beautiful_pair(nums1, nums2) returns a result r: it does not fail, overflow, go out of bounds, or panic.
    Preconditions: Let n = len(nums1). The arrays satisfy len(nums2) = n, 2 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums1[i] <= 100000 and 0 <= nums2[i] <= 100000. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (hlen : nums2.length = nums1.length)
      (hmin : 2 ≤ nums1.length)
      (hmax : nums1.length ≤ 100000)
      (hbound1 : AllValuesInRange nums1)
      (hbound2 : AllValuesInRange nums2) :
      ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulPair.beautiful_pair nums1 nums2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (hlen : nums2.length = nums1.length)
        (hmin : 2 ≤ nums1.length)
        (hmax : nums1.length ≤ 100000)
        (hbound1 : AllValuesInRange nums1)
        (hbound2 : AllValuesInRange nums2), ∃ r : alloc.vec.Vec Std.I64, Aegis.BeautifulPair.beautiful_pair nums1 nums2 = ok r) := by
    sorry

  end AegisSpec.BeautifulPair
