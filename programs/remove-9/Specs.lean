import Aegis.NewInteger.Code.Funs
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Specifications of `Aegis.NewInteger.new_integer`

LeetCode problem `remove-9`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NewInteger

  def DecimalNoNine (m : ℕ) : Prop := 9 ∉ Nat.digits 10 m

  def DecimalNoNineInt (z : ℤ) : Prop := DecimalNoNine z.natAbs

  def DecimalHasNine (m : ℕ) : Prop := 9 ∈ Nat.digits 10 m

  instance decidableDecimalNoNine (m : ℕ) : Decidable (DecimalNoNine m) := by
    unfold DecimalNoNine
    infer_instance

  instance decidableDecimalHasNine (m : ℕ) : Decidable (DecimalHasNine m) := by
    unfold DecimalHasNine
    infer_instance

  instance decidableDecimalNoNineInt (z : ℤ) : Decidable (DecimalNoNineInt z) := by
    unfold DecimalNoNineInt
    infer_instance

  def countNoNine (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter (fun m => DecimalNoNine m)).card

  def countNine (N : ℕ) : ℕ := ((Finset.Icc 1 N).filter (fun m => DecimalHasNine m)).card

  /-- The function returns a result r such that r >= 1, the decimal representation of r contains no digit 9, and the number of positive integers k with 1 <= k <= r whose decimal representation contains no digit 9 is exactly n.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧
          1 ≤ r.val ∧
            DecimalNoNineInt r.val ∧
              countNoNine r.val.toNat = n.val.toNat := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧
            1 ≤ r.val ∧
              DecimalNoNineInt r.val ∧
                countNoNine r.val.toNat = n.val.toNat) := by
    sorry

  /-- The function returns a result r and r >= n.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧ n.val ≤ r.val := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧ n.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and r <= 2052305618.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧ r.val ≤ 2052305618 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧ r.val ≤ 2052305618) := by
    sorry

  /-- Write n in base 9 as n = d_k * 9^k + d_{k-1} * 9^{k-1} + ... + d_0 * 9^0, where k >= 0, 0 <= d_i <= 8 for all i, and d_k > 0. Then the function returns r = d_k * 10^k + d_{k-1} * 10^{k-1} + ... + d_0 * 10^0.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_4 (n : Std.I64) (ds : List ℕ)
      (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000)
      (hne : ds ≠ []) (hpos : 0 < ds.getLast hne)
      (hdig : ∀ d ∈ ds, d ≤ 8)
      (hbase : (Nat.ofDigits 9 ds : ℤ) = n.val) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧ (Nat.ofDigits 10 ds : ℤ) = r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (ds : List ℕ)
        (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000)
        (hne : ds ≠ []) (hpos : 0 < ds.getLast hne)
        (hdig : ∀ d ∈ ds, d ≤ 8)
        (hbase : (Nat.ofDigits 9 ds : ℤ) = n.val), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧ (Nat.ofDigits 10 ds : ℤ) = r.val) := by
    sorry

  /-- For every n with 1 <= n <= 800000000, the function returns a result (it does not fail).
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_5 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64, Aegis.NewInteger.new_integer n = ok r := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64, Aegis.NewInteger.new_integer n = ok r) := by
    sorry

  /-- The function returns a result r and r - n equals the number of positive integers k with 1 <= k <= r whose decimal representation contains the digit 9.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_6 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧ r.val - n.val = (countNine r.val.toNat : ℤ) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧ r.val - n.val = (countNine r.val.toNat : ℤ)) := by
    sorry

  /-- If the function returns r1 on input n1 and r2 on input n2, then r1 < r2.
    Preconditions: 1 <= n1 < n2 <= 800000000 -/
  theorem spec_7 (n1 n2 r1 r2 : Std.I64)
      (hn1 : 1 ≤ n1.val) (hlt : n1.val < n2.val) (hn2 : n2.val ≤ 800000000)
      (h1 : Aegis.NewInteger.new_integer n1 = ok r1)
      (h2 : Aegis.NewInteger.new_integer n2 = ok r2) :
      r1.val < r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n1 n2 r1 r2 : Std.I64)
        (hn1 : 1 ≤ n1.val) (hlt : n1.val < n2.val) (hn2 : n2.val ≤ 800000000)
        (h1 : Aegis.NewInteger.new_integer n1 = ok r1)
        (h2 : Aegis.NewInteger.new_integer n2 = ok r2), r1.val < r2.val) := by
    sorry

  /-- The function returns a result r and r is the smallest positive integer such that the number of positive integers k with 1 <= k <= r whose decimal representation contains no digit 9 is exactly n.
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧
          1 ≤ r.val ∧
            countNoNine r.val.toNat = n.val.toNat ∧
              ∀ m : ℤ, 1 ≤ m → countNoNine m.toNat = n.val.toNat → r.val ≤ m := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧
            1 ≤ r.val ∧
              countNoNine r.val.toNat = n.val.toNat ∧
                ∀ m : ℤ, 1 ≤ m → countNoNine m.toNat = n.val.toNat → r.val ≤ m) := by
    sorry

  /-- Let k be the unique non-negative integer such that 9^k <= n < 9^(k+1). Then the function returns a result r with 10^k <= r < 10^(k+1).
    Preconditions: 1 <= n <= 800000000 -/
  theorem spec_9 (n : Std.I64) (k : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000)
      (hk1 : (9 : ℤ) ^ k ≤ n.val) (hk2 : n.val < (9 : ℤ) ^ (k + 1)) :
      ∃ r : Std.I64,
        Aegis.NewInteger.new_integer n = ok r ∧
          (10 : ℤ) ^ k ≤ r.val ∧ r.val < (10 : ℤ) ^ (k + 1) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (k : ℕ) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 800000000)
        (hk1 : (9 : ℤ) ^ k ≤ n.val) (hk2 : n.val < (9 : ℤ) ^ (k + 1)), ∃ r : Std.I64,
          Aegis.NewInteger.new_integer n = ok r ∧
            (10 : ℤ) ^ k ≤ r.val ∧ r.val < (10 : ℤ) ^ (k + 1)) := by
    sorry

  end AegisSpec.NewInteger
