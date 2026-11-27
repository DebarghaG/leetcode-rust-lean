import Aegis.MaxSum.Code.Funs

/-!
# Specifications of `Aegis.MaxSum.max_sum`

LeetCode problem `get-the-maximum-score`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaxSum

  def vals (s : Slice Std.I64) : List Int := s.val.map (fun x => x.val)

  def StrictInc (l : List Int) : Prop := l.Pairwise (fun x y => x < y)

  def ValuesInRange (l : List Int) : Prop := ∀ x, x ∈ l → 1 ≤ x ∧ x ≤ 10000000

  def WellFormed (l : List Int) : Prop :=
    1 ≤ l.length ∧ l.length ≤ 100000 ∧ StrictInc l ∧ ValuesInRange l

  def commonVals (l1 l2 : List Int) : List Int := (l1.filter (fun x => x ∈ l2)).dedup

  def inGap (x : Int) (lo hi : Option Int) : Bool :=
    (match lo with
      | none => true
      | some p => decide (p < x)) &&
    (match hi with
      | none => true
      | some c => decide (x ≤ c))

  def gapSum (l : List Int) (lo hi : Option Int) : Int :=
    (l.filter (fun x => inGap x lo hi)).sum

  def gapsOf (bounds : List Int) : List (Option Int × Option Int) :=
    (none :: bounds.map some).zip (bounds.map some ++ [none])

  def maxScore (l1 l2 : List Int) : Int :=
    ((gapsOf (commonVals l1 l2)).map
      (fun p => max (gapSum l1 p.1 p.2) (gapSum l2 p.1 p.2))).sum

  /-- Let a valid path be any sequence obtained by choosing nums1 or nums2 as the starting array, traversing that array from index 0 to the right, and at any value that occurs in both arrays optionally switching to the other array at that value, counting each value in the path once (in particular a switch value is counted only once); the traversal must continue to the end of the array on which it finishes. Let M be the maximum, over all valid paths, of the sum of the values in the path, each value counted once. Then max_sum nums1 nums2 returns a result r and r = M mod 1000000007, where the exact integer M is computed before the modulo reduction. Moreover M <= 2 * 100000 * 10000000 = 2 * 10^12, so M fits in i64.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; and 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i. -/
  theorem spec_1 (nums1 nums2 : Slice Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2)) :
      ∃ r : Std.I64,
        Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
        r.val = maxScore (vals nums1) (vals nums2) % 1000000007 ∧
        maxScore (vals nums1) (vals nums2) ≤ 2 * 100000 * 10000000 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2)), ∃ r : Std.I64,
          Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
          r.val = maxScore (vals nums1) (vals nums2) % 1000000007 ∧
          maxScore (vals nums1) (vals nums2) ≤ 2 * 100000 * 10000000) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, max_sum nums1 nums2 returns a result r; it does not panic, fail, or overflow. In particular, the exact maximum score M is at most 2 * 10^12 < 2^63, and the final residue is less than 1000000007.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; and 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i. -/
  theorem spec_2 (nums1 nums2 : Slice Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2)) :
      ∃ r : Std.I64,
        Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
        0 ≤ r.val ∧
        r.val < 1000000007 ∧
        maxScore (vals nums1) (vals nums2) ≤ 2 * 100000 * 10000000 ∧
        maxScore (vals nums1) (vals nums2) < 2 ^ 63 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2)), ∃ r : Std.I64,
          Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
          0 ≤ r.val ∧
          r.val < 1000000007 ∧
          maxScore (vals nums1) (vals nums2) ≤ 2 * 100000 * 10000000 ∧
          maxScore (vals nums1) (vals nums2) < 2 ^ 63) := by
    sorry

  /-- Whenever max_sum nums1 nums2 returns a result r, 0 <= r < 1000000007.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; and 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i. -/
  theorem spec_3 (nums1 nums2 : Slice Std.I64) (r : Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
      (hr : Aegis.MaxSum.max_sum nums1 nums2 = ok r) :
      0 ≤ r.val ∧ r.val < 1000000007 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (r : Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
        (hr : Aegis.MaxSum.max_sum nums1 nums2 = ok r), 0 ≤ r.val ∧ r.val < 1000000007) := by
    sorry

  /-- max_sum nums1 nums2 returns a result r and r = max(Σ_{i=0}^{len(nums1)-1} nums1[i], Σ_{i=0}^{len(nums2)-1} nums2[i]) mod 1000000007.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i; and nums1 and nums2 have no value in common. -/
  theorem spec_4 (nums1 nums2 : Slice Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
      (hdisj : ∀ x, x ∈ vals nums1 → x ∉ vals nums2) :
      ∃ r : Std.I64,
        Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
        r.val = max (vals nums1).sum (vals nums2).sum % 1000000007 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
        (hdisj : ∀ x, x ∈ vals nums1 → x ∉ vals nums2), ∃ r : Std.I64,
          Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
          r.val = max (vals nums1).sum (vals nums2).sum % 1000000007) := by
    sorry

  /-- Let P1 = Σ_{x in nums1, x <= c} x, P2 = Σ_{x in nums2, x <= c} x, S1 = Σ_{x in nums1, x > c} x, and S2 = Σ_{x in nums2, x > c} x. Then max_sum nums1 nums2 returns a result r and r = (max(P1, P2) + max(S1, spec_2)) mod 1000000007.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i; and exactly one integer c occurs in both nums1 and nums2. -/
  theorem spec_5 (nums1 nums2 : Slice Std.I64) (c : Int)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
      (hc1 : c ∈ vals nums1) (hc2 : c ∈ vals nums2)
      (huniq : ∀ x, x ∈ vals nums1 → x ∈ vals nums2 → x = c) :
      ∃ r : Std.I64,
        Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
        let P1 := gapSum (vals nums1) none (some c)
        let P2 := gapSum (vals nums2) none (some c)
        let S1 := gapSum (vals nums1) (some c) none
        let S2 := gapSum (vals nums2) (some c) none
        r.val = (max P1 P2 + max S1 S2) % 1000000007 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (c : Int)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
        (hc1 : c ∈ vals nums1) (hc2 : c ∈ vals nums2)
        (huniq : ∀ x, x ∈ vals nums1 → x ∈ vals nums2 → x = c), ∃ r : Std.I64,
          Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
          let P1 := gapSum (vals nums1) none (some c)
          let P2 := gapSum (vals nums2) none (some c)
          let S1 := gapSum (vals nums1) (some c) none
          let S2 := gapSum (vals nums2) (some c) none
          r.val = (max P1 P2 + max S1 S2) % 1000000007) := by
    sorry

  /-- Let A be nums2 if every value of nums1 occurs in nums2; otherwise let A be nums1. Then max_sum nums1 nums2 returns a result r and r = (Σ_{i=0}^{len(A)-1} A[i]) mod 1000000007.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i; and either every value of nums1 occurs in nums2, or every value of nums2 occurs in nums1. -/
  theorem spec_6 (nums1 nums2 : Slice Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
      (h : (∀ x, x ∈ vals nums1 → x ∈ vals nums2) ∨ (∀ x, x ∈ vals nums2 → x ∈ vals nums1)) :
      ∃ r : Std.I64,
        Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
        r.val = (if (∀ x, x ∈ vals nums1 → x ∈ vals nums2)
                   then (vals nums2).sum
                   else (vals nums1).sum) % 1000000007 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
        (h : (∀ x, x ∈ vals nums1 → x ∈ vals nums2) ∨ (∀ x, x ∈ vals nums2 → x ∈ vals nums1)), ∃ r : Std.I64,
          Aegis.MaxSum.max_sum nums1 nums2 = ok r ∧
          r.val = (if (∀ x, x ∈ vals nums1 → x ∈ vals nums2)
                     then (vals nums2).sum
                     else (vals nums1).sum) % 1000000007) := by
    sorry

  /-- For every nums1 and nums2 satisfying the preconditions, if max_sum nums1 nums2 returns r and max_sum nums2 nums1 returns s, then r = s.
    Preconditions: nums1 and nums2 are nonempty strictly increasing arrays of integers; 1 <= len(nums1), len(nums2) <= 100000; and 1 <= nums1[i], nums2[i] <= 10000000 for every valid index i. -/
  theorem spec_7 (nums1 nums2 : Slice Std.I64) (r s : Std.I64)
      (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
      (hr : Aegis.MaxSum.max_sum nums1 nums2 = ok r)
      (hs : Aegis.MaxSum.max_sum nums2 nums1 = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums1 nums2 : Slice Std.I64) (r s : Std.I64)
        (h1 : WellFormed (vals nums1)) (h2 : WellFormed (vals nums2))
        (hr : Aegis.MaxSum.max_sum nums1 nums2 = ok r)
        (hs : Aegis.MaxSum.max_sum nums2 nums1 = ok s), r.val = s.val) := by
    sorry

  end AegisSpec.MaxSum
