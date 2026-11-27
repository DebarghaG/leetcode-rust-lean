import Aegis.CheckPowersOfThree.Code.Funs

/-!
# Specifications of `Aegis.CheckPowersOfThree.check_powers_of_three`

LeetCode problem `check-if-number-is-a-sum-of-powers-of-three`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CheckPowersOfThree

  open Aeneas.Std.Result

  def IsSumOfPowersOfThree (n : ℤ) : Prop :=
    ∃ S : Finset ℕ, n = ∑ k ∈ S, (3 : ℤ) ^ k

  def TernaryDigitsAtMostOne (n : ℤ) : Prop :=
    ∀ k : ℕ, (n / (3 : ℤ) ^ k) % 3 = 0 ∨ (n / (3 : ℤ) ^ k) % 3 = 1

  /-- Whenever check_powers_of_three n returns a result r, r is true if and only if there exists a finite set S of nonnegative integers such that n equals the sum of 3^k over all k in S (with 3^0 = 1); r is false otherwise.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_1 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        (r = true ↔ IsSumOfPowersOfThree n.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          (r = true ↔ IsSumOfPowersOfThree n.val)) := by
    sorry

  /-- check_powers_of_three n returns a result r; it does not fail, panic, overflow, or go out of bounds.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_2 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7) :
      ∃ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7), ∃ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r) := by
    sorry

  /-- Whenever check_powers_of_three n returns a result r with r = true, n <= 7,174,453.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_3 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = true →
        n.val ≤ 7174453 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = true →
          n.val ≤ 7174453) := by
    sorry

  /-- Whenever check_powers_of_three n returns a result r with r = true, there exists a finite set S of integers such that every j in S satisfies 0 <= j <= k-1 and (n mod 3^k) equals the sum of 3^j over all j in S.
    Preconditions: 1 <= n <= 10^7 and k is an integer with 1 <= k <= 14. -/
  theorem spec_4 (n : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
      (hklo : 1 ≤ k) (hkhi : k ≤ 14) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = true →
        ∃ S : Finset ℕ, (∀ j ∈ S, j < k) ∧
          n.val % (3 : ℤ) ^ k = ∑ j ∈ S, (3 : ℤ) ^ j := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
        (hklo : 1 ≤ k) (hkhi : k ≤ 14), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = true →
          ∃ S : Finset ℕ, (∀ j ∈ S, j < k) ∧
            n.val % (3 : ℤ) ^ k = ∑ j ∈ S, (3 : ℤ) ^ j) := by
    sorry

  /-- Let r be the result of check_powers_of_three n and let r' be the result of check_powers_of_three (3^k * n). Whenever both return results, r = r'.
    Preconditions: 1 <= n <= 10^7, k is a nonnegative integer, and 1 <= 3^k * n <= 10^7. -/
  theorem spec_5 (n m : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
      (hmul_lo : 1 ≤ 3 ^ k * n.val) (hmul_hi : 3 ^ k * n.val ≤ 10 ^ 7)
      (hm : m.val = 3 ^ k * n.val) :
      ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r' := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
        (hmul_lo : 1 ≤ 3 ^ k * n.val) (hmul_hi : 3 ^ k * n.val ≤ 10 ^ 7)
        (hm : m.val = 3 ^ k * n.val), ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r') := by
    sorry

  /-- Let r be the result of check_powers_of_three n and let r' be the result of check_powers_of_three ((n - 1) / 3). Whenever both return results, r = r'.
    Preconditions: 4 <= n <= 10^7 and n mod 3 = 1. -/
  theorem spec_6 (n m : Std.I64) (hnlo : 4 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
      (hnmod : n.val % 3 = 1) (hm : m.val = (n.val - 1) / 3) :
      ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m : Std.I64) (hnlo : 4 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
        (hnmod : n.val % 3 = 1) (hm : m.val = (n.val - 1) / 3), ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r') := by
    sorry

  /-- Let r be the result of check_powers_of_three n and let r' be the result of check_powers_of_three (n + 3^k). Whenever both return results, r = r'.
    Preconditions: 1 <= n <= 10^7, k is a nonnegative integer, n < 3^k, and n + 3^k <= 10^7. -/
  theorem spec_7 (n m : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
      (hlt : n.val < 3 ^ k) (hsum : n.val + 3 ^ k ≤ 10 ^ 7)
      (hm : m.val = n.val + 3 ^ k) :
      ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r' := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m : Std.I64) (k : ℕ) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
        (hlt : n.val < 3 ^ k) (hsum : n.val + 3 ^ k ≤ 10 ^ 7)
        (hm : m.val = n.val + 3 ^ k), ∀ r r', Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          Aegis.CheckPowersOfThree.check_powers_of_three m = ok r' → r = r') := by
    sorry

  /-- Whenever check_powers_of_three n returns a result r, r is true if and only if n = 1.
    Preconditions: 1 <= n <= 2. -/
  theorem spec_8 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 2) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        (r = true ↔ n.val = 1) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 2), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          (r = true ↔ n.val = 1)) := by
    sorry

  /-- Whenever check_powers_of_three n returns a result r, r = true if and only if for every nonnegative integer k, the k-th ternary digit ((n / 3^k) mod 3) is 0 or 1; equivalently, the base-3 representation of n contains no digit 2.
    Preconditions: 1 <= n <= 10^7. -/
  theorem spec_9 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
        (r = true ↔ TernaryDigitsAtMostOne n.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r →
          (r = true ↔ TernaryDigitsAtMostOne n.val)) := by
    sorry

  /-- Whenever check_powers_of_three n returns a result r, r = false.
    Preconditions: 1 <= n <= 10^7 and n mod 3 = 2. -/
  theorem spec_10 (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
      (hnmod : n.val % 3 = 2) :
      ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = false := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hnlo : 1 ≤ n.val) (hnhi : n.val ≤ 10 ^ 7)
        (hnmod : n.val % 3 = 2), ∀ r, Aegis.CheckPowersOfThree.check_powers_of_three n = ok r → r = false) := by
    sorry

  end AegisSpec.CheckPowersOfThree
