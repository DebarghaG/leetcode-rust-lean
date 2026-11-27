import Aegis.NumDupDigitsAtMostN.Code.Funs

/-!
# Specifications of `Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n`

LeetCode problem `numbers-with-repeated-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumDupDigitsAtMostN

  def digitList (x : Nat) : List Nat :=
    if h : x = 0 then [] else x % 10 :: digitList (x / 10)
  termination_by x
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

  def hasRepeatedDigitB (x : Nat) : Bool :=
    (digitList x).any (fun d => decide (2 ≤ (digitList x).count d))

  def HasRepeatedDigit (x : Nat) : Prop := hasRepeatedDigitB x = true

  def HasAllDigitsDistinct (x : Nat) : Prop :=
    1 ≤ x ∧ hasRepeatedDigitB x = false

  def countRepeatedDigitsUpTo (n : Nat) : Nat :=
    ((Finset.Icc 1 n).filter (fun x => hasRepeatedDigitB x = true)).card

  def countDistinctDigitsUpTo (n : Nat) : Nat :=
    ((Finset.Icc 1 n).filter (fun x => hasRepeatedDigitB x = false)).card

  /-- The function returns a result r (it does not fail), and r equals the cardinality of the set { x : 1 <= x <= n and x has a repeated digit }, where a positive integer x has a repeated digit if, in its decimal representation without leading zeros, some digit occurs at least twice.
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_1 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∃ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r ∧
          r.val = ((countRepeatedDigitsUpTo n.val.toNat : Nat) : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∃ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r ∧
            r.val = ((countRepeatedDigitsUpTo n.val.toNat : Nat) : Int)) := by
    sorry

  /-- The function returns a result r (it does not fail, panic, or overflow).
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∃ r : Std.I64, Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∃ r : Std.I64, Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n - 1.
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_3 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          0 ≤ r.val ∧ r.val ≤ n.val - 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            0 ≤ r.val ∧ r.val ≤ n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, r = n / 11, where / denotes integer division (floor).
    Preconditions: 1 <= n <= 99. -/
  theorem spec_4 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 99) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          r.val = n.val / 11 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 99), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            r.val = n.val / 11) := by
    sorry

  /-- Whenever the function returns a result r, r + d = n, where d is the number of integers x with 1 <= x <= n whose decimal representation without leading zeros has all digits distinct (no digit occurs more than once).
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_5 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          r.val + ((countDistinctDigitsUpTo n.val.toNat : Nat) : Int) = n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            r.val + ((countDistinctDigitsUpTo n.val.toNat : Nat) : Int) = n.val) := by
    sorry

  /-- If r1 is the result of the function on n1 and r2 is the result of the function on n2, then r1 <= r2.
    Preconditions: 1 <= n1 <= n2 <= 10^9. -/
  theorem spec_6 (n1 n2 : Std.I64)
      (h1 : 1 ≤ n1.val ∧ n1.val ≤ n2.val) (h2 : n2.val ≤ 1000000000) :
      ∀ r1 r2 : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n1 = ok r1 →
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n2 = ok r2 →
            r1.val ≤ r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n1 n2 : Std.I64)
        (h1 : 1 ≤ n1.val ∧ n1.val ≤ n2.val) (h2 : n2.val ≤ 1000000000), ∀ r1 r2 : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n1 = ok r1 →
            Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n2 = ok r2 →
              r1.val ≤ r2.val) := by
    sorry

  /-- If r is the result of the function on n and r' is the result of the function on n+1, then r' - r = 1 when the decimal representation of n+1 without leading zeros contains a digit at least twice, and r' - r = 0 otherwise.
    Preconditions: 1 <= n < 10^9. -/
  theorem spec_7 (n nsucc : Std.I64)
      (hn : 1 ≤ n.val ∧ n.val < 1000000000) (hsucc : nsucc.val = n.val + 1) :
      ∀ r r' : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n nsucc = ok r' →
            ((HasRepeatedDigit (n.val.toNat + 1) → r'.val - r.val = 1) ∧
              (¬ HasRepeatedDigit (n.val.toNat + 1) → r'.val - r.val = 0)) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n nsucc : Std.I64)
        (hn : 1 ≤ n.val ∧ n.val < 1000000000) (hsucc : nsucc.val = n.val + 1), ∀ r r' : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n nsucc = ok r' →
              ((HasRepeatedDigit (n.val.toNat + 1) → r'.val - r.val = 1) ∧
                (¬ HasRepeatedDigit (n.val.toNat + 1) → r'.val - r.val = 0))) := by
    sorry

  /-- Whenever the function returns a result r, r >= n - 5611770.
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_8 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          r.val ≥ n.val - 5611770 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            r.val ≥ n.val - 5611770) := by
    sorry

  /-- Whenever the function returns a result r, r <= 994388230.
    Preconditions: 1 <= n <= 10^9. -/
  theorem spec_9 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
          r.val ≤ 994388230 := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r →
            r.val ≤ 994388230) := by
    sorry

  /-- Whenever the function returns a result r, r >= 1.
    Preconditions: 11 <= n <= 10^9. -/
  theorem spec_10 (n : Std.I64) (hn : 11 ≤ n.val ∧ n.val ≤ 1000000000) :
      ∀ r : Std.I64,
        Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r → 1 ≤ r.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (hn : 11 ≤ n.val ∧ n.val ≤ 1000000000), ∀ r : Std.I64,
          Aegis.NumDupDigitsAtMostN.num_dup_digits_at_most_n n = ok r → 1 ≤ r.val) := by
    sorry

  end AegisSpec.NumDupDigitsAtMostN
