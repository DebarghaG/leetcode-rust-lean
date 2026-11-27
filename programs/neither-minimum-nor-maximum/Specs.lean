import Aegis.FindNonMinOrMax.Code.Funs

/-!
# Specifications of `Aegis.FindNonMinOrMax.find_non_min_or_max`

LeetCode problem `neither-minimum-nor-maximum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindNonMinOrMax

  def lenBounds (nums : Slice Std.I64) : Prop :=
    1 ≤ nums.val.length ∧ nums.val.length ≤ 100

  def elementsInRange (nums : Slice Std.I64) : Prop :=
    ∀ (i : Nat) (hi : i < nums.val.length), 1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 100

  def pairwiseDistinct (nums : Slice Std.I64) : Prop :=
    ∀ (i j : Nat) (hi : i < nums.val.length) (hj : j < nums.val.length), i ≠ j →
      (nums.val[i]).val ≠ (nums.val[j]).val

  def hasBelow (nums : Slice Std.I64) (r : Int) : Prop :=
    ∃ (p : Nat) (hp : p < nums.val.length), (nums.val[p]).val < r

  def hasAbove (nums : Slice Std.I64) (r : Int) : Prop :=
    ∃ (q : Nat) (hq : q < nums.val.length), r < (nums.val[q]).val

  def hasNonExtremalEntry (nums : Slice Std.I64) : Prop :=
    ∃ (i : Nat) (hi : i < nums.val.length),
      hasBelow nums (nums.val[i]).val ∧ hasAbove nums (nums.val[i]).val

  /-- The function returns a result r, and: if len(nums) <= 2, then r = -1; if len(nums) >= 3, then there exists an index i with 0 <= i < len(nums) such that nums[i] = r, and there exist indices p and q with 0 <= p < len(nums) and 0 <= q < len(nums) such that nums[p] < r and nums[q] > r.
    Preconditions: 1 <= len(nums) <= 100; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hrange : elementsInRange nums)
      (hdist : pairwiseDistinct nums) :
      ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧
        (nums.val.length ≤ 2 → r.val = -1) ∧
        (3 ≤ nums.val.length →
          (∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = r.val) ∧
          hasBelow nums r.val ∧ hasAbove nums r.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hrange : elementsInRange nums)
        (hdist : pairwiseDistinct nums), ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧
          (nums.val.length ≤ 2 → r.val = -1) ∧
          (3 ≤ nums.val.length →
            (∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = r.val) ∧
            hasBelow nums r.val ∧ hasAbove nums r.val)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: 1 <= len(nums) <= 100; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hrange : elementsInRange nums)
      (hdist : pairwiseDistinct nums) :
      ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hrange : elementsInRange nums)
        (hdist : pairwiseDistinct nums), ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= 100.
    Preconditions: 1 <= len(nums) <= 100; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hrange : elementsInRange nums)
      (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
        r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 100) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hrange : elementsInRange nums)
        (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
          r.val = -1 ∨ (1 ≤ r.val ∧ r.val ≤ 100)) := by
    sorry

  /-- The function returns a result r and r = -1.
    Preconditions: 1 <= len(nums) <= 100; len(nums) = 1; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen1 : nums.val.length = 1)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧ r.val = -1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen1 : nums.val.length = 1)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧ r.val = -1) := by
    sorry

  /-- The function returns a result r and r != -1.
    Preconditions: 1 <= len(nums) <= 100; len(nums) >= 3; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧ r.val ≠ -1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∃ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r ∧ r.val ≠ -1) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if there is no index i with 0 <= i < len(nums) for which both (there exists p with 0 <= p < len(nums) and nums[p] < nums[i]) and (there exists q with 0 <= q < len(nums) and nums[q] > nums[i]).
    Preconditions: 1 <= len(nums) <= 100; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hrange : elementsInRange nums)
      (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
        (r.val = -1 ↔ ¬ hasNonExtremalEntry nums) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hrange : elementsInRange nums)
        (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
          (r.val = -1 ↔ ¬ hasNonExtremalEntry nums)) := by
    sorry

  /-- Whenever the function returns a result r and r != -1, there exists an index i with 0 <= i < len(nums) such that nums[i] = r.
    Preconditions: 1 <= len(nums) <= 100; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hrange : elementsInRange nums)
      (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → r.val ≠ -1 →
        ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hrange : elementsInRange nums)
        (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → r.val ≠ -1 →
          ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index p with 0 <= p < len(nums) such that nums[p] < r.
    Preconditions: 1 <= len(nums) <= 100; len(nums) >= 3; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → hasBelow nums r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → hasBelow nums r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an index q with 0 <= q < len(nums) such that nums[q] > r.
    Preconditions: 1 <= len(nums) <= 100; len(nums) >= 3; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_9 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → hasAbove nums r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r → hasAbove nums r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist indices a, b, c with 0 <= a < 3, 0 <= b < 3, and 0 <= c < 3 such that nums[a] < nums[b] < nums[c] and r = nums[b].
    Preconditions: 1 <= len(nums) <= 100; len(nums) = 3; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_10 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen3 : nums.val.length = 3)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
        ∃ (a b c : Nat) (ha : a < 3) (hb : b < 3) (hc : c < 3),
          (nums.val[a]).val < (nums.val[b]).val ∧
          (nums.val[b]).val < (nums.val[c]).val ∧
          r.val = (nums.val[b]).val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen3 : nums.val.length = 3)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
          ∃ (a b c : Nat) (ha : a < 3) (hb : b < 3) (hc : c < 3),
            (nums.val[a]).val < (nums.val[b]).val ∧
            (nums.val[b]).val < (nums.val[c]).val ∧
            r.val = (nums.val[b]).val) := by
    sorry

  /-- Whenever the function returns a result r, there exist pairwise distinct indices i, p, q with 0 <= i < len(nums), 0 <= p < len(nums), and 0 <= q < len(nums) such that nums[i] = r, nums[p] < r, and nums[q] > r.
    Preconditions: 1 <= len(nums) <= 100; len(nums) >= 3; for every index i with 0 <= i < len(nums), 1 <= nums[i] <= 100; for all indices i and j with 0 <= i < len(nums) and 0 <= j < len(nums), if i != j then nums[i] != nums[j]. -/
  theorem spec_11 (nums : Slice Std.I64)
      (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
      (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums) :
      ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
        ∃ (i p q : Nat) (hi : i < nums.val.length) (hp : p < nums.val.length)
          (hq : q < nums.val.length),
          i ≠ p ∧ i ≠ q ∧ p ≠ q ∧
          (nums.val[i]).val = r.val ∧
          (nums.val[p]).val < r.val ∧
          r.val < (nums.val[q]).val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hlen : lenBounds nums) (hlen3 : 3 ≤ nums.val.length)
        (hrange : elementsInRange nums) (hdist : pairwiseDistinct nums), ∀ r, Aegis.FindNonMinOrMax.find_non_min_or_max nums = ok r →
          ∃ (i p q : Nat) (hi : i < nums.val.length) (hp : p < nums.val.length)
            (hq : q < nums.val.length),
            i ≠ p ∧ i ≠ q ∧ p ≠ q ∧
            (nums.val[i]).val = r.val ∧
            (nums.val[p]).val < r.val ∧
            r.val < (nums.val[q]).val) := by
    sorry

  end AegisSpec.FindNonMinOrMax
