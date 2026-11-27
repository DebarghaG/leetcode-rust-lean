import Aegis.AccountBalanceAfterPurchase.Code.Funs

/-!
# Specifications of `Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase`

LeetCode problem `account-balance-after-rounded-purchase`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AccountBalanceAfterPurchase

def roundedMultipleOfTen (p : ℤ) : ℤ := 10 * ((p + 5) / 10)

def IsNearestMultipleOfTen (p R : ℤ) : Prop :=
  10 ∣ R ∧
    (∀ R' : ℤ, 10 ∣ R' → |p - R| ≤ |p - R'|) ∧
      (∀ R' : ℤ, 10 ∣ R' → |p - R'| = |p - R| → R' ≤ R)

/-- The function returns a result r such that r = 100 - R, where R is the unique integer satisfying all of the following: (1) R is a multiple of 10; (2) |purchaseAmount - R| is minimal among all multiples of 10; (3) if purchaseAmount is exactly midway between two multiples of 10, then R is the larger of those two. Equivalently, R = 10 * floor((purchaseAmount + 5) / 10), with floor division on nonnegative integers, and r = 100 - R.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_1 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∃ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r ∧
        IsNearestMultipleOfTen purchaseAmount.val (100 - r.val) ∧
          (100 - r.val) = roundedMultipleOfTen purchaseAmount.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∃ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r ∧
        IsNearestMultipleOfTen purchaseAmount.val (100 - r.val) ∧
          (100 - r.val) = roundedMultipleOfTen purchaseAmount.val) := by
  sorry

/-- For every purchaseAmount satisfying the precondition, the function returns a result r; in particular it does not fail with an overflow, panic, or out-of-bounds error.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_2 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∃ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∃ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, 0 <= r <= 100.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_3 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        0 ≤ r.val ∧ r.val ≤ 100 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        0 ≤ r.val ∧ r.val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, the deducted amount 100 - r is a multiple of 10, i.e. (100 - r) mod 10 = 0 when residues are taken in {0,1,2,3,4,5,6,7,8,9}.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_4 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (100 - r.val) % 10 = 0 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (100 - r.val) % 10 = 0) := by
  sorry

/-- If the function returns r_a on input a and r_b on input b, then r_a >= r_b.
  Preconditions: 0 <= a <= 100, 0 <= b <= 100, and a <= b. -/
theorem spec_5 (a b : I64) (ha_lo : 0 ≤ a.val) (ha_hi : a.val ≤ 100) (hb_lo : 0 ≤ b.val)
    (hb_hi : b.val ≤ 100) (hab : a.val ≤ b.val) :
    ∀ ra rb : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase a = ok ra →
        Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase b = ok rb → rb.val ≤ ra.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (a b : I64) (ha_lo : 0 ≤ a.val) (ha_hi : a.val ≤ 100) (hb_lo : 0 ≤ b.val)
    (hb_hi : b.val ≤ 100) (hab : a.val ≤ b.val), ∀ ra rb : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase a = ok ra →
        Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase b = ok rb → rb.val ≤ ra.val) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, with R = 100 - r, we have |purchaseAmount - R| <= 5.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_6 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        |purchaseAmount.val - (100 - r.val)| ≤ 5 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        |purchaseAmount.val - (100 - r.val)| ≤ 5) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, r = 100 if and only if 0 <= purchaseAmount <= 4.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_7 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (r.val = 100 ↔ 0 ≤ purchaseAmount.val ∧ purchaseAmount.val ≤ 4) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (r.val = 100 ↔ 0 ≤ purchaseAmount.val ∧ purchaseAmount.val ≤ 4)) := by
  sorry

/-- Whenever the function returns a result r on an input satisfying the precondition, r = 0 if and only if 95 <= purchaseAmount <= 100.
  Preconditions: 0 <= purchaseAmount <= 100, where purchaseAmount denotes the mathematical integer value of the I64 argument. -/
theorem spec_8 (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100) :
    ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (r.val = 0 ↔ 95 ≤ purchaseAmount.val ∧ purchaseAmount.val ≤ 100) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (purchaseAmount : I64) (h_lo : 0 ≤ purchaseAmount.val)
    (h_hi : purchaseAmount.val ≤ 100), ∀ r : I64,
      Aegis.AccountBalanceAfterPurchase.account_balance_after_purchase purchaseAmount = ok r →
        (r.val = 0 ↔ 95 ≤ purchaseAmount.val ∧ purchaseAmount.val ≤ 100)) := by
  sorry

end AegisSpec.AccountBalanceAfterPurchase
