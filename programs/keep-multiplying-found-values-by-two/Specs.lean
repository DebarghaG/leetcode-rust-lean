import Aegis.FindFinalValue.Code.Funs

/-!
# Specifications of `Aegis.FindFinalValue.find_final_value`

LeetCode problem `keep-multiplying-found-values-by-two`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindFinalValue

  def occurs (nums : Slice Std.I64) (x : Int) : Prop :=
    ∃ (i : Nat) (hi : i < nums.val.length), (nums.val[i]).val = x

  /-- Let 'x is present in nums' mean that there exists an index i with 0 <= i < len(nums) and nums[i] = x. The function returns a result r, and there exists an integer k >= 0 such that (1) r = original * 2^k, (2) for every integer j with 0 <= j < k, original * 2^j is present in nums, and (3) r is not present in nums. Equivalently, k is the least nonnegative integer for which original * 2^k is not present in nums, and r is that value.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_1 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r ∧
        ∃ k : Nat,
          r.val = original.val * 2 ^ k ∧
          (∀ j : Nat, j < k → occurs nums (original.val * 2 ^ j)) ∧
          ¬ occurs nums r.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∃ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r ∧
          ∃ k : Nat,
            r.val = original.val * 2 ^ k ∧
            (∀ j : Nat, j < k → occurs nums (original.val * 2 ^ j)) ∧
            ¬ occurs nums r.val) := by
    sorry

  /-- The function returns a result r (it does not fail) for every input satisfying the preconditions.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_2 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∃ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 2000.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_3 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64,
        Aegis.FindFinalValue.find_final_value nums original = ok r → 1 ≤ r.val ∧ r.val ≤ 2000 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64,
          Aegis.FindFinalValue.find_final_value nums original = ok r → 1 ≤ r.val ∧ r.val ≤ 2000) := by
    sorry

  /-- Whenever the function returns a result r, r is not present in nums (that is, there is no index i with 0 <= i < len(nums) and nums[i] = r).
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_4 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64,
        Aegis.FindFinalValue.find_final_value nums original = ok r → ¬ occurs nums r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64,
          Aegis.FindFinalValue.find_final_value nums original = ok r → ¬ occurs nums r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer k >= 0 such that r = original * 2^k.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_5 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        ∃ k : Nat, r.val = original.val * 2 ^ k := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          ∃ k : Nat, r.val = original.val * 2 ^ k) := by
    sorry

  /-- Whenever the function returns a result r, for every integer j >= 0 with original * 2^j < r, the value original * 2^j is present in nums (that is, there exists an index i with 0 <= i < len(nums) and nums[i] = original * 2^j).
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_6 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        ∀ j : Nat, original.val * 2 ^ j < r.val → occurs nums (original.val * 2 ^ j) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          ∀ j : Nat, original.val * 2 ^ j < r.val → occurs nums (original.val * 2 ^ j)) := by
    sorry

  /-- Whenever the function returns a result r with r != original, r is even and r/2 is present in nums (that is, there exists an index i with 0 <= i < len(nums) and nums[i] = r/2).
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_7 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        r.val ≠ original.val → r.val % 2 = 0 ∧ occurs nums (r.val / 2) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          r.val ≠ original.val → r.val % 2 = 0 ∧ occurs nums (r.val / 2)) := by
    sorry

  /-- Whenever the function returns a result r, r = original if and only if original is not present in nums (that is, there is no index i with 0 <= i < len(nums) and nums[i] = original).
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_8 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        (r.val = original.val ↔ ¬ occurs nums original.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          (r.val = original.val ↔ ¬ occurs nums original.val)) := by
    sorry

  /-- Whenever the function returns a result r, if original is present in nums (i.e., there exists i with 0 <= i < len(nums) and nums[i] = original) and 2 * original is not present in nums (i.e., there is no i with 0 <= i < len(nums) and nums[i] = 2 * original), then r = 2 * original.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_9 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        occurs nums original.val → ¬ occurs nums (2 * original.val) →
          r.val = 2 * original.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          occurs nums original.val → ¬ occurs nums (2 * original.val) →
            r.val = 2 * original.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer j >= 0 with original * 2^j <= 2000, if original * 2^j is not present in nums (i.e., there is no index i with 0 <= i < len(nums) and nums[i] = original * 2^j), then r <= original * 2^j.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_10 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        ∀ j : Nat, original.val * 2 ^ j ≤ 2000 → ¬ occurs nums (original.val * 2 ^ j) →
          r.val ≤ original.val * 2 ^ j := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          ∀ j : Nat, original.val * 2 ^ j ≤ 2000 → ¬ occurs nums (original.val * 2 ^ j) →
            r.val ≤ original.val * 2 ^ j) := by
    sorry

  /-- Let 'x is present in nums' mean that there exists an index i with 0 <= i < len(nums) and nums[i] = x, and similarly for nums'. If for every integer x, x is present in nums if and only if x is present in nums', then whenever find_final_value(nums, original) returns a result r, find_final_value(nums', original) also returns r.
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. Also nums' is any slice with len(nums') between 1 and 1000 inclusive and, for every i with 0 <= i < len(nums'), 1 <= nums'[i] <= 1000. -/
  theorem spec_11 (nums nums' : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000)
      (hlen' : 1 ≤ nums'.val.length ∧ nums'.val.length ≤ 1000)
      (hvals' : ∀ (i : Nat) (hi : i < nums'.val.length),
        1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000)
      (hsame : ∀ x : Int, occurs nums x ↔ occurs nums' x) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        Aegis.FindFinalValue.find_final_value nums' original = ok r := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (nums nums' : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000)
        (hlen' : 1 ≤ nums'.val.length ∧ nums'.val.length ≤ 1000)
        (hvals' : ∀ (i : Nat) (hi : i < nums'.val.length),
          1 ≤ (nums'.val[i]).val ∧ (nums'.val[i]).val ≤ 1000)
        (hsame : ∀ x : Int, occurs nums x ↔ occurs nums' x), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          Aegis.FindFinalValue.find_final_value nums' original = ok r) := by
    sorry

  /-- Whenever the function returns a result r, for every integer m >= 0, if original * 2^j is present in nums (i.e., there exists an index i with 0 <= i < len(nums) and nums[i] = original * 2^j) for every integer j with 0 <= j <= m, then r >= original * 2^(m+1).
    Preconditions: len(nums) is between 1 and 1000 inclusive; for every i with 0 <= i < len(nums), 1 <= nums[i] <= 1000; 1 <= original <= 1000. -/
  theorem spec_12 (nums : Slice Std.I64) (original : Std.I64)
      (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
      (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
        1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
      (horig : 1 ≤ original.val ∧ original.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
        ∀ m : Nat,
          (∀ j : Nat, j ≤ m → occurs nums (original.val * 2 ^ j)) →
          original.val * 2 ^ (m + 1) ≤ r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (nums : Slice Std.I64) (original : Std.I64)
        (hlen : 1 ≤ nums.val.length ∧ nums.val.length ≤ 1000)
        (hvals : ∀ (i : Nat) (hi : i < nums.val.length),
          1 ≤ (nums.val[i]).val ∧ (nums.val[i]).val ≤ 1000)
        (horig : 1 ≤ original.val ∧ original.val ≤ 1000), ∀ r : Std.I64, Aegis.FindFinalValue.find_final_value nums original = ok r →
          ∀ m : Nat,
            (∀ j : Nat, j ≤ m → occurs nums (original.val * 2 ^ j)) →
            original.val * 2 ^ (m + 1) ≤ r.val) := by
    sorry

  end AegisSpec.FindFinalValue
