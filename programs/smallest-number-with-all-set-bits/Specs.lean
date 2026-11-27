import Aegis.SmallestNumber.Code.Funs

/-!
# Specifications of `Aegis.SmallestNumber.smallest_number`

LeetCode problem `smallest-number-with-all-set-bits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestNumber

  def IsLeastExponent (n : ℤ) (L : ℕ) : Prop :=
    1 ≤ L ∧ n ≤ 2 ^ L - 1 ∧ ∀ j : ℕ, 1 ≤ j → n ≤ 2 ^ j - 1 → L ≤ j

  /-- The function returns a result r, and r is the minimum integer x such that x ≥ n and x = 2^k - 1 for some integer k ≥ 1. Equivalently: r ≥ n; there exists an integer K ≥ 1 with r = 2^K - 1; and for every integer j ≥ 1 with 2^j - 1 ≥ n, r ≤ 2^j - 1.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∃ r : Std.I64,
        Aegis.SmallestNumber.smallest_number n = ok r ∧
          n.val ≤ r.val ∧
          (∃ K : ℕ, 1 ≤ K ∧ r.val = 2 ^ K - 1) ∧
          (∀ j : ℕ, 1 ≤ j → n.val ≤ 2 ^ j - 1 → r.val ≤ 2 ^ j - 1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∃ r : Std.I64,
          Aegis.SmallestNumber.smallest_number n = ok r ∧
            n.val ≤ r.val ∧
            (∃ K : ℕ, 1 ≤ K ∧ r.val = 2 ^ K - 1) ∧
            (∀ j : ℕ, 1 ≤ j → n.val ≤ 2 ^ j - 1 → r.val ≤ 2 ^ j - 1)) := by
    sorry

  /-- The function returns a result r; it does not fail, overflow, or panic on any such n.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∃ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r ≥ n.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → n.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → n.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, there exists an integer k ≥ 1 such that r = 2^k - 1; equivalently, the binary representation of r consists only of 1 bits.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r →
        ∃ k : ℕ, 1 ≤ k ∧ r.val = 2 ^ k - 1 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r →
          ∃ k : ℕ, 1 ≤ k ∧ r.val = 2 ^ k - 1) := by
    sorry

  /-- Whenever the function returns a result r, for every integer j ≥ 1 with 2^j - 1 ≥ n, we have r ≤ 2^j - 1.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r →
        ∀ j : ℕ, 1 ≤ j → n.val ≤ 2 ^ j - 1 → r.val ≤ 2 ^ j - 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r →
          ∀ j : ℕ, 1 ≤ j → n.val ≤ 2 ^ j - 1 → r.val ≤ 2 ^ j - 1) := by
    sorry

  /-- Let L be the least positive integer such that n ≤ 2^L - 1. Whenever the function returns a result r, r = 2^L - 1.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_6 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ L : ℕ, IsLeastExponent n.val L →
        ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = 2 ^ L - 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ L : ℕ, IsLeastExponent n.val L →
          ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = 2 ^ L - 1) := by
    sorry

  /-- Whenever the function returns a result r, r ≤ 1023.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_7 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val ≤ 1023 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val ≤ 1023) := by
    sorry

  /-- Whenever the function returns a result r, r < 2 * n.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val < 2 * n.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val < 2 * n.val) := by
    sorry

  /-- If n = 2^k - 1 for some integer k ≥ 1, then whenever the function returns a result r, r = n.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000)
      (h : ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = n.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000)
        (h : ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = n.val) := by
    sorry

  /-- If there is no integer k ≥ 1 with n = 2^k - 1, then whenever the function returns a result r, r > n.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_10 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000)
      (h : ¬ ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1) :
      ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → n.val < r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000)
        (h : ¬ ∃ k : ℕ, 1 ≤ k ∧ n.val = 2 ^ k - 1), ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → n.val < r.val) := by
    sorry

  /-- For every integer k ≥ 1, if 2^(k-1) ≤ n ≤ 2^k - 1, then whenever the function returns a result r, r = 2^k - 1.
    Preconditions: The 64-bit integer n satisfies 1 ≤ n ≤ 1000. -/
  theorem spec_11 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000) :
      ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ n.val → n.val ≤ 2 ^ k - 1 →
        ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = 2 ^ k - 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000), ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ n.val → n.val ≤ 2 ^ k - 1 →
          ∀ r : Std.I64, Aegis.SmallestNumber.smallest_number n = ok r → r.val = 2 ^ k - 1) := by
    sorry

  end AegisSpec.SmallestNumber
