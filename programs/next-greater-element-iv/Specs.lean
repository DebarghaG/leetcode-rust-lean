import Aegis.SecondGreaterElement.Code.Funs

/-!
# Specifications of `Aegis.SecondGreaterElement.second_greater_element`

LeetCode problem `next-greater-element-iv`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
  open Aegis.SecondGreaterElement

  namespace AegisSpec.SecondGreaterElement

  def greaterIndices (l : List Std.I64) (i : Nat) : List Nat :=
    (List.range l.length).filter fun j => decide (i < j ∧ (l[i]!).val < (l[j]!).val)

  def countGreater (l : List Std.I64) (i : Nat) : Nat := (greaterIndices l i).length

  def countGreaterBetween (l : List Std.I64) (i j : Nat) : Nat :=
    ((greaterIndices l i).filter fun k => k < j).length

  def IsFirstGreater (l : List Std.I64) (i j : Nat) : Prop :=
    i < j ∧ j < l.length ∧ (l[i]!).val < (l[j]!).val ∧
      ∀ k, i < k → k < j → ¬ ((l[i]!).val < (l[k]!).val)

  def IsLeastGreaterAfter (l : List Std.I64) (i after j : Nat) : Prop :=
    after < j ∧ j < l.length ∧ (l[i]!).val < (l[j]!).val ∧
      ∀ k, after < k → k < j → ¬ ((l[i]!).val < (l[k]!).val)

  /-- Whenever second_greater_element nums returns a result r, len(r) = n, and for every i with 0 <= i < n, letting G_i = { j | i < j < n and nums[j] > nums[i] }: if |G_i| >= 2 and j1 is the least element of G_i and j2 is the least element of G_i with j2 > j1, then r[i] = nums[j2]; if |G_i| < 2, then r[i] = -1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        r.val.length = nums.val.length ∧
          ∀ i, i < nums.val.length →
            (2 ≤ countGreater nums.val i →
                ∀ j1 j2, IsFirstGreater nums.val i j1 →
                  IsLeastGreaterAfter nums.val i j1 j2 →
                  (r.val[i]!).val = (nums.val[j2]!).val) ∧
            (countGreater nums.val i < 2 → (r.val[i]!).val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          r.val.length = nums.val.length ∧
            ∀ i, i < nums.val.length →
              (2 ≤ countGreater nums.val i →
                  ∀ j1 j2, IsFirstGreater nums.val i j1 →
                    IsLeastGreaterAfter nums.val i j1 j2 →
                    (r.val[i]!).val = (nums.val[j2]!).val) ∧
              (countGreater nums.val i < 2 → (r.val[i]!).val = -1)) := by
    sorry

  /-- For every nums satisfying the preconditions, second_greater_element nums returns a result r; execution does not fail by overflow, panic, or out-of-bounds access.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∃ r, second_greater_element nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∃ r, second_greater_element nums = ok r) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i with 0 <= i < n, either r[i] = -1 or 0 <= r[i] <= 1000000000.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i, i < nums.val.length →
          (r.val[i]!).val = -1 ∨
            (0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 1000000000) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i, i < nums.val.length →
            (r.val[i]!).val = -1 ∨
              (0 ≤ (r.val[i]!).val ∧ (r.val[i]!).val ≤ 1000000000)) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i with 0 <= i < n, if r[i] != -1 then r[i] > nums[i].
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i, i < nums.val.length →
          (r.val[i]!).val ≠ -1 → (nums.val[i]!).val < (r.val[i]!).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i, i < nums.val.length →
            (r.val[i]!).val ≠ -1 → (nums.val[i]!).val < (r.val[i]!).val) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i with 0 <= i < n, r[i] = -1 if and only if the number of indices j with i < j < n and nums[j] > nums[i] is less than 2.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i, i < nums.val.length →
          ((r.val[i]!).val = -1 ↔ countGreater nums.val i < 2) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i, i < nums.val.length →
            ((r.val[i]!).val = -1 ↔ countGreater nums.val i < 2)) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i with 0 <= i < n, if r[i] != -1 then there exists an index j such that i < j < n, nums[j] = r[i], nums[j] > nums[i], and the number of indices k with i < k < j and nums[k] > nums[i] is exactly 1.
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i, i < nums.val.length →
          (r.val[i]!).val ≠ -1 →
            ∃ j, i < j ∧ j < nums.val.length ∧
              (nums.val[j]!).val = (r.val[i]!).val ∧
              (nums.val[i]!).val < (nums.val[j]!).val ∧
              countGreaterBetween nums.val i j = 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i, i < nums.val.length →
            (r.val[i]!).val ≠ -1 →
              ∃ j, i < j ∧ j < nums.val.length ∧
                (nums.val[j]!).val = (r.val[i]!).val ∧
                (nums.val[i]!).val < (nums.val[j]!).val ∧
                countGreaterBetween nums.val i j = 1) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i and every j with 0 <= i < n, i < j < n, nums[j] > nums[i], and the number of indices k with i < k < j and nums[k] > nums[i] exactly 1, we have r[i] = nums[j].
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i j, i < nums.val.length → i < j → j < nums.val.length →
          (nums.val[i]!).val < (nums.val[j]!).val →
          countGreaterBetween nums.val i j = 1 →
          (r.val[i]!).val = (nums.val[j]!).val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i j, i < nums.val.length → i < j → j < nums.val.length →
            (nums.val[i]!).val < (nums.val[j]!).val →
            countGreaterBetween nums.val i j = 1 →
            (r.val[i]!).val = (nums.val[j]!).val) := by
    sorry

  /-- Whenever second_greater_element nums returns a result r, for every i with 0 <= i < n, if there are at least two indices j with i < j < n and nums[j] > nums[i], and if j1 is the least such index and j2 is the least index satisfying j1 < j2 < n and nums[j2] > nums[i], then r[i] = nums[j2].
    Preconditions: Let n = len(nums). 1 <= n <= 100000, and for every i with 0 <= i < n, 0 <= nums[i] <= 1000000000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
      (hval : ∀ i, i < nums.val.length →
        0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000) :
      ∀ r, second_greater_element nums = ok r →
        ∀ i, i < nums.val.length → 2 ≤ countGreater nums.val i →
          ∀ j1 j2, IsFirstGreater nums.val i j1 → IsLeastGreaterAfter nums.val i j1 j2 →
            (r.val[i]!).val = (nums.val[j2]!).val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hpos : 1 ≤ nums.val.length) (hcap : nums.val.length ≤ 100000)
        (hval : ∀ i, i < nums.val.length →
          0 ≤ (nums.val[i]!).val ∧ (nums.val[i]!).val ≤ 1000000000), ∀ r, second_greater_element nums = ok r →
          ∀ i, i < nums.val.length → 2 ≤ countGreater nums.val i →
            ∀ j1 j2, IsFirstGreater nums.val i j1 → IsLeastGreaterAfter nums.val i j1 j2 →
              (r.val[i]!).val = (nums.val[j2]!).val) := by
    sorry

  end AegisSpec.SecondGreaterElement
