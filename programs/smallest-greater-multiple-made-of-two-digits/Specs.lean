import Aegis.FindInteger.Code.Funs

/-!
# Specifications of `Aegis.FindInteger.find_integer`

LeetCode problem `smallest-greater-multiple-made-of-two-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.FindInteger

  def decDigitsFuel : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, n => if n = 0 then [] else n % 10 :: decDigitsFuel fuel (n / 10)

  def decDigits (n : Nat) : List Nat := (decDigitsFuel (n + 1) n).reverse

  def decimalDigits (n : Int) : List Int := (decDigits n.toNat).map (fun d => (d : Int))

  def mostSignificantDigit (n : Int) : Option Int := (decimalDigits n).head?

  def admissible (k d1 d2 n : Int) : Prop :=
    k < n ∧ n ≤ 2147483647 ∧ n % k = 0 ∧ ∀ x ∈ decimalDigits n, x = d1 ∨ x = d2

  def IsLeastAdmissible (k d1 d2 m : Int) : Prop :=
    admissible k d1 d2 m ∧ ∀ n : Int, admissible k d1 d2 n → m ≤ n

  def HasAdmissible (k d1 d2 : Int) : Prop := ∃ n : Int, admissible k d1 d2 n

  /-- Define an integer n to be admissible if k < n <= 2147483647, n mod k = 0, and every digit in the standard base-10 representation of n (written without leading zeros) is equal to digit1 or digit2. Let A be the set of all admissible integers. The function returns Result.ok r for some i64 r, and r satisfies: if A is nonempty, then r = min A; if A is empty, then r = -1.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9, with k, digit1, and digit2 represented as 64-bit signed integers. -/
  theorem spec_1 (k digit1 digit2 : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9) :
      ∃ r : I64,
        Aegis.FindInteger.find_integer k digit1 digit2 = ok r ∧
          (HasAdmissible k.val digit1.val digit2.val →
            IsLeastAdmissible k.val digit1.val digit2.val r.val) ∧
          (¬ HasAdmissible k.val digit1.val digit2.val → r.val = -1) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (k digit1 digit2 : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9), ∃ r : I64,
          Aegis.FindInteger.find_integer k digit1 digit2 = ok r ∧
            (HasAdmissible k.val digit1.val digit2.val →
              IsLeastAdmissible k.val digit1.val digit2.val r.val) ∧
            (¬ HasAdmissible k.val digit1.val digit2.val → r.val = -1)) := by
    sorry

  /-- For every input satisfying the preconditions, find_integer k digit1 digit2 returns a value Result.ok r for some i64 r; it does not fail due to overflow, panic, or out-of-bounds access.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_2 (k digit1 digit2 : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9) :
      ∃ r : I64, Aegis.FindInteger.find_integer k digit1 digit2 = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (k digit1 digit2 : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9), ∃ r : I64, Aegis.FindInteger.find_integer k digit1 digit2 = ok r) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, it holds that k < r <= 2147483647.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_3 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      k.val < r.val ∧ r.val ≤ 2147483647 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), k.val < r.val ∧ r.val ≤ 2147483647) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, there exists an integer q such that 2 <= q <= floor(2147483647 / k) and r = k * q.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_4 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      ∃ q : Int, 2 ≤ q ∧ q ≤ 2147483647 / k.val ∧ r.val = k.val * q := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), ∃ q : Int, 2 ≤ q ∧ q ≤ 2147483647 / k.val ∧ r.val = k.val * q) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, every digit in the standard base-10 representation of r, written without leading zeros, is equal to digit1 or equal to digit2.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_5 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      ∀ x ∈ decimalDigits r.val, x = digit1.val ∨ x = digit2.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), ∀ x ∈ decimalDigits r.val, x = digit1.val ∨ x = digit2.val) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, for every integer n with k < n < r, n is not admissible, where admissible means n <= 2147483647, n mod k = 0, and every decimal digit of n is digit1 or digit2.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_6 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      ∀ n : Int, k.val < n → n < r.val → ¬ admissible k.val digit1.val digit2.val n := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), ∀ n : Int, k.val < n → n < r.val → ¬ admissible k.val digit1.val digit2.val n) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r = -1, there is no integer n such that k < n <= 2147483647, n mod k = 0, and every digit in the standard decimal representation of n is equal to digit1 or digit2.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_7 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hisneg : r.val = -1) :
      ¬ HasAdmissible k.val digit1.val digit2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hisneg : r.val = -1), ¬ HasAdmissible k.val digit1.val digit2.val) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r, if there exists an integer n such that k < n <= 2147483647, n mod k = 0, and every decimal digit of n is digit1 or digit2, then r != -1.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_8 (k digit1 digit2 r : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hwit : HasAdmissible k.val digit1.val digit2.val) :
      r.val ≠ -1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (k digit1 digit2 r : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hwit : HasAdmissible k.val digit1.val digit2.val), r.val ≠ -1) := by
    sorry

  /-- find_integer k digit1 digit2 returns Result.ok (-1).
    Preconditions: 1 <= k <= 1000 and digit1 = 0 and digit2 = 0. -/
  theorem spec_9 (k digit1 digit2 : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1 : digit1.val = 0) (hd2 : digit2.val = 0) :
      Aegis.FindInteger.find_integer k digit1 digit2 = ok ((-1)#i64) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (k digit1 digit2 : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1 : digit1.val = 0) (hd2 : digit2.val = 0), Aegis.FindInteger.find_integer k digit1 digit2 = ok ((-1)#i64)) := by
    sorry

  /-- For every valid input, find_integer k digit1 digit2 and find_integer k digit2 digit1 return equal Result values.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, and 0 <= digit2 <= 9. -/
  theorem spec_10 (k digit1 digit2 : I64)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9) :
      Aegis.FindInteger.find_integer k digit1 digit2 =
        Aegis.FindInteger.find_integer k digit2 digit1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (k digit1 digit2 : I64)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9), Aegis.FindInteger.find_integer k digit1 digit2 =
          Aegis.FindInteger.find_integer k digit2 digit1) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, the most significant decimal digit of r is d.
    Preconditions: 1 <= k <= 1000, 0 <= digit1 <= 9, 0 <= digit2 <= 9, and exactly one of digit1 and digit2 is nonzero; let d denote that nonzero digit. -/
  theorem spec_11 (k digit1 digit2 : I64) (d : Int)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
      (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
      (hexcl : (digit1.val = d ∧ digit2.val = 0) ∨ (digit1.val = 0 ∧ digit2.val = d))
      (hd_nz : d ≠ 0)
      (r : I64)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      mostSignificantDigit r.val = some d := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (k digit1 digit2 : I64) (d : Int)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1_lb : 0 ≤ digit1.val) (hd1_ub : digit1.val ≤ 9)
        (hd2_lb : 0 ≤ digit2.val) (hd2_ub : digit2.val ≤ 9)
        (hexcl : (digit1.val = d ∧ digit2.val = 0) ∨ (digit1.val = 0 ∧ digit2.val = d))
        (hd_nz : d ≠ 0)
        (r : I64)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), mostSignificantDigit r.val = some d) := by
    sorry

  /-- Whenever find_integer k digit1 digit2 returns Result.ok r with r != -1, every digit in the standard decimal representation of r equals d; equivalently, r is a repdigit consisting of one or more copies of d.
    Preconditions: 1 <= k <= 1000 and digit1 = digit2 = d with 1 <= d <= 9. -/
  theorem spec_12 (k digit1 digit2 : I64) (d : Int)
      (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
      (hd1 : digit1.val = d) (hd2 : digit2.val = d)
      (hd_lb : 1 ≤ d) (hd_ub : d ≤ 9)
      (r : I64)
      (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
      (hne : r.val ≠ -1) :
      ∀ x ∈ decimalDigits r.val, x = d := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (k digit1 digit2 : I64) (d : Int)
        (hk_lb : 1 ≤ k.val) (hk_ub : k.val ≤ 1000)
        (hd1 : digit1.val = d) (hd2 : digit2.val = d)
        (hd_lb : 1 ≤ d) (hd_ub : d ≤ 9)
        (r : I64)
        (hr : Aegis.FindInteger.find_integer k digit1 digit2 = ok r)
        (hne : r.val ≠ -1), ∀ x ∈ decimalDigits r.val, x = d) := by
    sorry

  end AegisSpec.FindInteger
