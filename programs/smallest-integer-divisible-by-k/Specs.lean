import Aegis.SmallestRepunitDivByK.Code.Funs

/-!
# Specifications of `Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k`

LeetCode problem `smallest-integer-divisible-by-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestRepunitDivByK

  def repunit (L : Nat) : Int := (10 ^ L - 1) / 9

  def repunit_dvd (k : Std.I64) (L : Nat) : Prop := k.val ∣ repunit L

  /-- Let R(L), for every positive integer L, be the mathematical integer (not restricted to the 64-bit range) whose decimal representation consists of exactly L copies of the digit 1; equivalently R(L) = (10^L - 1) / 9. Whenever the function returns a result r, exactly one of the following holds: (a) r = -1 and for every positive integer L, k does not divide R(L); or (b) r >= 1, k divides R(r), and for every positive integer L with 1 <= L < r, k does not divide R(L).
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_1 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r) :
      (r.val = -1 ∧ ∀ L : Nat, 1 <= L → ¬ repunit_dvd k L) ∨
      (1 <= r.val ∧ repunit_dvd k r.val.toNat ∧
        ∀ L : Nat, 1 <= L → L < r.val.toNat → ¬ repunit_dvd k L) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r), (r.val = -1 ∧ ∀ L : Nat, 1 <= L → ¬ repunit_dvd k L) ∨
        (1 <= r.val ∧ repunit_dvd k r.val.toNat ∧
          ∀ L : Nat, 1 <= L → L < r.val.toNat → ¬ repunit_dvd k L)) := by
    sorry

  /-- The function returns a result r (it does not fail: no arithmetic overflow, out-of-bounds access, or panic) for every k satisfying the precondition.
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_2 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) :
      ∃ r, Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000), ∃ r, Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = -1 or 1 <= r <= k.
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_3 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r) :
      r.val = -1 ∨ (1 <= r.val ∧ r.val <= k.val) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r), r.val = -1 ∨ (1 <= r.val ∧ r.val <= k.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = -1 if and only if k is divisible by 2 or k is divisible by 5 (that is, k mod 2 = 0 or k mod 5 = 0).
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_4 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r) :
      (r.val = -1 ↔ (2 : Int) ∣ k.val ∨ (5 : Int) ∣ k.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r), (r.val = -1 ↔ (2 : Int) ∣ k.val ∨ (5 : Int) ∣ k.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if k = 1.
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_5 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r) :
      (r.val = 1 ↔ k.val = 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r), (r.val = 1 ↔ k.val = 1)) := by
    sorry

  /-- Let R(L) be the mathematical integer whose decimal representation is L copies of digit 1, for L >= 1. Whenever the function returns a result r with r >= 1, every positive integer L such that k divides R(L) satisfies r <= L.
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_6 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r)
      (hr1 : 1 <= r.val) :
      ∀ L : Nat, 1 <= L → repunit_dvd k L → r.val.toNat <= L := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r)
        (hr1 : 1 <= r.val), ∀ L : Nat, 1 <= L → repunit_dvd k L → r.val.toNat <= L) := by
    sorry

  /-- Let R(L) be the mathematical integer whose decimal representation is L copies of digit 1, for L >= 1. Whenever the function returns a result r with r >= 1, the mathematical integer 10^r - 1 is divisible by 9*k.
    Preconditions: 1 <= k <= 100000 (k is an i64). -/
  theorem spec_7 (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
      (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r)
      (hr1 : 1 <= r.val) :
      9 * k.val ∣ 10 ^ r.val.toNat - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k : Std.I64) (hk1 : 1 <= k.val) (hk2 : k.val <= 100000) (r : Std.I64)
        (hr : Aegis.SmallestRepunitDivByK.smallest_repunit_div_by_k k = ok r)
        (hr1 : 1 <= r.val), 9 * k.val ∣ 10 ^ r.val.toNat - 1) := by
    sorry

  end AegisSpec.SmallestRepunitDivByK
