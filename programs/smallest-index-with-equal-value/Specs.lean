import Aegis.SmallestEqual.Code.Funs

/-!
# Specifications of `Aegis.SmallestEqual.smallest_equal`

LeetCode problem `smallest-index-with-equal-value`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestEqual

  /-- The function returns a result r and: (a) if there exists an index i with 0 <= i < len(nums) and i mod 10 == nums[i], then 0 <= r < len(nums), r mod 10 == nums[r], and for every j with 0 <= j < r, j mod 10 != nums[j]; (b) if no such index i exists, then r == -1.
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∃ r : I64,
        Aegis.SmallestEqual.smallest_equal nums = ok r ∧
          ((∃ i : Nat, i < nums.val.length ∧ (i : Int) % 10 = (nums.val[i]!).val) →
            0 ≤ r.val ∧ r.val < (nums.val.length : Int) ∧
              r.val % 10 = (nums.val[r.val.toNat]!).val ∧
              ∀ j : Nat, (j : Int) < r.val → (j : Int) % 10 ≠ (nums.val[j]!).val) ∧
          (¬ (∃ i : Nat, i < nums.val.length ∧ (i : Int) % 10 = (nums.val[i]!).val) →
            r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∃ r : I64,
          Aegis.SmallestEqual.smallest_equal nums = ok r ∧
            ((∃ i : Nat, i < nums.val.length ∧ (i : Int) % 10 = (nums.val[i]!).val) →
              0 ≤ r.val ∧ r.val < (nums.val.length : Int) ∧
                r.val % 10 = (nums.val[r.val.toNat]!).val ∧
                ∀ j : Nat, (j : Int) < r.val → (j : Int) % 10 ≠ (nums.val[j]!).val) ∧
            (¬ (∃ i : Nat, i < nums.val.length ∧ (i : Int) % 10 = (nums.val[i]!).val) →
              r.val = -1)) := by
    sorry

  /-- The function returns a result r (it does not fail).
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∃ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∃ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r == -1 or (0 <= r < len(nums)).
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r →
        r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int)) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r →
          r.val = -1 ∨ (0 ≤ r.val ∧ r.val < (nums.val.length : Int))) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, it holds that r < len(nums) and r mod 10 == nums[r].
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → 0 ≤ r.val →
        r.val < (nums.val.length : Int) ∧ r.val % 10 = (nums.val[r.val.toNat]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → 0 ≤ r.val →
          r.val < (nums.val.length : Int) ∧ r.val % 10 = (nums.val[r.val.toNat]!).val) := by
    sorry

  /-- Whenever the function returns a result r with r >= 0, for every j with 0 <= j < r, j mod 10 != nums[j].
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → 0 ≤ r.val →
        ∀ j : Nat, (j : Int) < r.val → (j : Int) % 10 ≠ (nums.val[j]!).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → 0 ≤ r.val →
          ∀ j : Nat, (j : Int) < r.val → (j : Int) % 10 ≠ (nums.val[j]!).val) := by
    sorry

  /-- Whenever the function returns r == -1, for every i with 0 <= i < len(nums), i mod 10 != nums[i].
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_6 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → r.val = -1 →
        ∀ i : Nat, i < nums.val.length → (i : Int) % 10 ≠ (nums.val[i]!).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r → r.val = -1 →
          ∀ i : Nat, i < nums.val.length → (i : Int) % 10 ≠ (nums.val[i]!).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), if i mod 10 == nums[i], then r != -1 and r <= i.
    Preconditions: len(nums) >= 1 and len(nums) <= 100 and for every i with 0 <= i < len(nums), 0 <= nums[i] <= 9. -/
  theorem spec_7 (nums : Slice I64)
      (hlen_pos : 1 ≤ nums.val.length)
      (hlen_le : nums.val.length ≤ 100)
      (hvals : ∀ i : Nat, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9) :
      ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r →
        ∀ i : Nat, i < nums.val.length → (i : Int) % 10 = (nums.val[i]!).val →
          r.val ≠ -1 ∧ r.val ≤ (i : Int) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_pos : 1 ≤ nums.val.length)
        (hlen_le : nums.val.length ≤ 100)
        (hvals : ∀ i : Nat, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 9), ∀ r : I64, Aegis.SmallestEqual.smallest_equal nums = ok r →
          ∀ i : Nat, i < nums.val.length → (i : Int) % 10 = (nums.val[i]!).val →
            r.val ≠ -1 ∧ r.val ≤ (i : Int)) := by
    sorry

  end AegisSpec.SmallestEqual
