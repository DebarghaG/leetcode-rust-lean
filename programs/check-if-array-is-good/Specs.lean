import Aegis.IsGood.Code.Funs

/-!
# Specifications of `Aegis.IsGood.is_good`

LeetCode problem `check-if-array-is-good`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.IsGood

  def vals (nums : Slice I64) : List Int := nums.val.map (fun v => v.val)

  def countIn (l : List Int) (x : Int) : Nat :=
    (l.filter (fun v => decide (v = x))).length

  def IsMaxOf (l : List Int) (m : Int) : Prop := m ∈ l ∧ ∀ x ∈ l, x ≤ m

  /-- Whenever the function returns a result r, r is true if and only if len(nums) >= 2 and, with n = len(nums) - 1, for every integer x, the number of indices i with 0 <= i < len(nums) and nums[i] = x is: 2 if x = n; 1 if 1 <= x < n; and 0 otherwise. Equivalently, r is true exactly when nums is a permutation of base[n] = [1, 2, ..., n-1, n, n] for n = len(nums) - 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_1 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r →
        (r = true ↔ 2 ≤ nums.val.length ∧
          ∀ x : Int, countIn (vals nums) x =
            (if x = (nums.val.length : Int) - 1 then 2
             else if 1 ≤ x ∧ x < (nums.val.length : Int) - 1 then 1 else 0)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r →
          (r = true ↔ 2 ≤ nums.val.length ∧
            ∀ x : Int, countIn (vals nums) x =
              (if x = (nums.val.length : Int) - 1 then 2
               else if 1 ≤ x ∧ x < (nums.val.length : Int) - 1 then 1 else 0))) := by
    sorry

  /-- The function returns a result (some Bool) and does not fail: no panic, out-of-bounds access, or arithmetic overflow occurs on this input.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_2 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∃ r : Bool, Aegis.IsGood.is_good nums = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∃ r : Bool, Aegis.IsGood.is_good nums = ok r) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then len(nums) >= 2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_3 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true → 2 ≤ nums.val.length := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true → 2 ≤ nums.val.length) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then, letting n = len(nums) - 1, the maximum element of nums (the greatest value among nums[0], ..., nums[len(nums)-1]) is exactly n.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_4 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        IsMaxOf (vals nums) ((nums.val.length : Int) - 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          IsMaxOf (vals nums) ((nums.val.length : Int) - 1)) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then for every index i with 0 <= i < len(nums), 1 <= nums[i] <= len(nums) - 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_5 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int) - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          ∀ (i : Nat) (hi : i < nums.val.length),
            1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ (nums.val.length : Int) - 1) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then, letting n = len(nums) - 1, exactly two indices i satisfy 0 <= i < len(nums) and nums[i] = n.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_6 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        countIn (vals nums) ((nums.val.length : Int) - 1) = 2 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          countIn (vals nums) ((nums.val.length : Int) - 1) = 2) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then, letting n = len(nums) - 1, for every integer x with 1 <= x < n, exactly one index i satisfies 0 <= i < len(nums) and nums[i] = x.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_7 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        ∀ x : Int, 1 ≤ x → x < (nums.val.length : Int) - 1 → countIn (vals nums) x = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          ∀ x : Int, 1 ≤ x → x < (nums.val.length : Int) - 1 → countIn (vals nums) x = 1) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then the sum of all elements of nums equals (len(nums) - 1) * (len(nums) + 2) / 2.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_8 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        (vals nums).sum = ((nums.val.length : Int) - 1) * ((nums.val.length : Int) + 2) / 2 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          (vals nums).sum = ((nums.val.length : Int) - 1) * ((nums.val.length : Int) + 2) / 2) := by
    sorry

  /-- Whenever the function returns a result r, if r = true then the cardinality of the set {nums[i] | 0 <= i < len(nums)} is exactly len(nums) - 1.
    Preconditions: 1 <= len(nums) <= 100 and for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200. -/
  theorem spec_9 (nums : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200) :
      ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
        (vals nums).toFinset.card = nums.val.length - 1 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200), ∀ r : Bool, Aegis.IsGood.is_good nums = ok r → r = true →
          (vals nums).toFinset.card = nums.val.length - 1) := by
    sorry

  /-- For any two slices nums and nums' satisfying the constraints, if for every integer x the number of indices i with 0 <= i < len(nums) and nums[i] = x equals the number of indices i with 0 <= i < len(nums') and nums'[i] = x, then whenever is_good(nums) returns r and is_good(nums') returns r', we have r = r'.
    Preconditions: 1 <= len(nums) <= 100, 1 <= len(nums') <= 100, for every i with 0 <= i < len(nums), 1 <= nums[i] <= 200, and for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 200. -/
  theorem spec_10 (nums nums' : Slice I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
      (hlen_lo' : 1 ≤ nums'.val.length) (hlen_hi' : nums'.val.length ≤ 100)
      (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200)
      (hbound' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 200)
      (hsame : ∀ x : Int, countIn (vals nums) x = countIn (vals nums') x) :
      ∀ (r r' : Bool), Aegis.IsGood.is_good nums = ok r →
        Aegis.IsGood.is_good nums' = ok r' → r = r' := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums' : Slice I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100)
        (hlen_lo' : 1 ≤ nums'.val.length) (hlen_hi' : nums'.val.length ≤ 100)
        (hbound : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]'hi).val ∧ (nums.val[i]'hi).val ≤ 200)
        (hbound' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val[i]'hi).val ∧ (nums'.val[i]'hi).val ≤ 200)
        (hsame : ∀ x : Int, countIn (vals nums) x = countIn (vals nums') x), ∀ (r r' : Bool), Aegis.IsGood.is_good nums = ok r →
          Aegis.IsGood.is_good nums' = ok r' → r = r') := by
    sorry

  end AegisSpec.IsGood
