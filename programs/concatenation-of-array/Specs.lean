import Aegis.GetConcatenation.Code.Funs

/-!
# Specifications of `Aegis.GetConcatenation.get_concatenation`

LeetCode problem `concatenation-of-array`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.GetConcatenation

  def countValue (l : List Std.I64) (v : Int) : Nat :=
    l.countP (fun x => decide (x.val = v))

  /-- Whenever the function returns a result r, len(r) = 2*n and, for every i with 0 <= i < n, r[i] = nums[i] and r[i+n] = nums[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∃ (hlen : r.val.length = 2 * nums.val.length),
          ∀ (i : Nat) (hi : i < nums.val.length),
            (r.val[i]'(by omega)).val = (nums.val[i]'hi).val ∧
            (r.val[i + nums.val.length]'(by omega)).val = (nums.val[i]'hi).val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∃ (hlen : r.val.length = 2 * nums.val.length),
            ∀ (i : Nat) (hi : i < nums.val.length),
              (r.val[i]'(by omega)).val = (nums.val[i]'hi).val ∧
              (r.val[i + nums.val.length]'(by omega)).val = (nums.val[i]'hi).val) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a successful result (it does not fail).
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∃ r, Aegis.GetConcatenation.get_concatenation nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∃ r, Aegis.GetConcatenation.get_concatenation nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, len(r) = 2 * len(nums).
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        r.val.length = 2 * nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          r.val.length = 2 * nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), i < len(r) and r[i] = nums[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          ∃ (h : i < r.val.length), (r.val[i]'h).val = (nums.val[i]'hi).val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∀ (i : Nat) (hi : i < nums.val.length),
            ∃ (h : i < r.val.length), (r.val[i]'h).val = (nums.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), i + len(nums) < len(r) and r[i + len(nums)] = nums[i].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          ∃ (h : i + nums.val.length < r.val.length),
            (r.val[i + nums.val.length]'h).val = (nums.val[i]'hi).val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∀ (i : Nat) (hi : i < nums.val.length),
            ∃ (h : i + nums.val.length < r.val.length),
              (r.val[i + nums.val.length]'h).val = (nums.val[i]'hi).val) := by
    sorry

  /-- Whenever the function returns a result r, for every i with 0 <= i < len(nums), i + len(nums) < len(r) and r[i] = r[i + len(nums)].
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∀ (i : Nat) (hi : i < nums.val.length),
          ∃ (hlo : i < r.val.length) (hhi : i + nums.val.length < r.val.length),
            (r.val[i]'hlo).val = (r.val[i + nums.val.length]'hhi).val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∀ (i : Nat) (hi : i < nums.val.length),
            ∃ (hlo : i < r.val.length) (hhi : i + nums.val.length < r.val.length),
              (r.val[i]'hlo).val = (r.val[i + nums.val.length]'hhi).val) := by
    sorry

  /-- Whenever the function returns a result r, for every j with 0 <= j < len(r), 1 <= r[j] <= 1000.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∀ (j : Nat) (hj : j < r.val.length),
          1 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val ≤ 1000 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∀ (j : Nat) (hj : j < r.val.length),
            1 ≤ (r.val[j]'hj).val ∧ (r.val[j]'hj).val ≤ 1000) := by
    sorry

  /-- Whenever the function returns a result r, for every integer v, the number of indices j with 0 <= j < len(r) and r[j] = v equals twice the number of indices i with 0 <= i < len(nums) and nums[i] = v.
    Preconditions: Let n = len(nums). The preconditions are 1 <= n <= 1000 and, for every i with 0 <= i < n, 1 <= nums[i] <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000) :
      ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
        ∀ v : Int, countValue r.val v = 2 * countValue nums.val v := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hn_bounds : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 1000), ∀ r, Aegis.GetConcatenation.get_concatenation nums = ok r →
          ∀ v : Int, countValue r.val v = 2 * countValue nums.val v) := by
    sorry

  end AegisSpec.GetConcatenation
