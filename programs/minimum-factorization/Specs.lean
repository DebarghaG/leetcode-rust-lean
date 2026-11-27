import Aegis.SmallestFactorization.Code.Funs

/-!
# Specifications of `Aegis.SmallestFactorization.smallest_factorization`

LeetCode problem `minimum-factorization`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.SmallestFactorization

  open Aegis.SmallestFactorization (smallest_factorization)

  def digitsRev (n : Nat) : List Nat :=
    if n < 10 then [n] else n % 10 :: digitsRev (n / 10)
  termination_by n
  decreasing_by
    have hn : 0 < n := by omega
    exact Nat.div_lt_self hn (by omega)

  def digitsOfNat (n : Nat) : List Nat := (digitsRev n).reverse

  def digitsOf (z : Int) : List Nat := digitsOfNat z.natAbs

  def digitProdNat (n : Nat) : Nat := (digitsRev n).prod

  def digitProd (z : Int) : Int := (digitProdNat z.natAbs : Int)

  def HasDigitProdSolution (k : Int) : Prop :=
    ∃ y : Int, 1 ≤ y ∧ y ≤ 2147483647 ∧ digitProd y = k

  def IsLeastWithDigitProd (k : Int) (r : Int) : Prop :=
    1 ≤ r ∧ r ≤ 2147483647 ∧ digitProd r = k ∧
      ∀ y : Int, 1 ≤ y → y < r → digitProd y ≠ k

  /-- The function returns a result r such that: if there exists a positive integer y with 1 <= y <= 2147483647 and D(y) = num, then r is the least positive integer with D(r) = num (so D(r) = num, r <= 2147483647, and D(y) != num for every positive integer y < r); otherwise r = 0.
    Preconditions: num is an integer with 1 <= num <= 2147483647 (the problem's constraint). Let D(z) denote the product of the decimal digits of a positive integer z (for example, D(68)=48). -/
  theorem spec_1 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∃ r : Std.I64,
        smallest_factorization num = ok r ∧
          (HasDigitProdSolution num.val → IsLeastWithDigitProd num.val r.val) ∧
          (¬ HasDigitProdSolution num.val → r.val = 0) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∃ r : Std.I64,
          smallest_factorization num = ok r ∧
            (HasDigitProdSolution num.val → IsLeastWithDigitProd num.val r.val) ∧
            (¬ HasDigitProdSolution num.val → r.val = 0)) := by
    sorry

  /-- The function returns a result r; it does not fail (no overflow, out-of-bounds, or panic).
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_2 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∃ r : Std.I64, smallest_factorization num = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∃ r : Std.I64, smallest_factorization num = ok r) := by
    sorry

  /-- Whenever the function returns a result r, either r = 0 or 1 <= r <= 2147483647.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_3 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r →
          r.val = 0 ∨ (1 ≤ r.val ∧ r.val ≤ 2147483647) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r →
            r.val = 0 ∨ (1 ≤ r.val ∧ r.val ≤ 2147483647)) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, D(r) = num.
    Preconditions: 1 <= num <= 2147483647. Let D(z) be the product of the decimal digits of positive integer z. -/
  theorem spec_4 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 → digitProd r.val = num.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 → digitProd r.val = num.val) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, for every positive integer y with y < r, D(y) != num.
    Preconditions: 1 <= num <= 2147483647. Let D(z) be the product of the decimal digits of positive integer z. -/
  theorem spec_5 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          ∀ y : Int, 1 ≤ y → y < r.val → digitProd y ≠ num.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            ∀ y : Int, 1 ≤ y → y < r.val → digitProd y ≠ num.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if there is no positive integer y with 1 <= y <= 2147483647 and D(y) = num.
    Preconditions: 1 <= num <= 2147483647. Let D(z) be the product of the decimal digits of positive integer z. -/
  theorem spec_6 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r →
          (r.val = 0 ↔ ¬ HasDigitProdSolution num.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r →
            (r.val = 0 ↔ ¬ HasDigitProdSolution num.val)) := by
    sorry

  /-- The function returns r = num.
    Preconditions: 1 <= num <= 9. -/
  theorem spec_7 (num : Std.I64) (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 9) :
      ∃ r : Std.I64, smallest_factorization num = ok r ∧ r.val = num.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val) (hnum_hi : num.val ≤ 9), ∃ r : Std.I64, smallest_factorization num = ok r ∧ r.val = num.val) := by
    sorry

  /-- If there exists a prime p such that p divides num and p is not one of 2, 3, 5, 7, then the function returns r = 0.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_8 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647)
      (hbad : ∃ p : Nat,
        Nat.Prime p ∧ (p : Int) ∣ num.val ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7) :
      ∃ r : Std.I64, smallest_factorization num = ok r ∧ r.val = 0 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647)
        (hbad : ∃ p : Nat,
          Nat.Prime p ∧ (p : Int) ∣ num.val ∧ p ≠ 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 7), ∃ r : Std.I64, smallest_factorization num = ok r ∧ r.val = 0) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, the decimal digits of r, read from most significant to least significant, are nondecreasing.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_9 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          (digitsOf r.val).Pairwise (fun a b => a ≤ b) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            (digitsOf r.val).Pairwise (fun a b => a ≤ b)) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, no decimal digit of r is 0.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_10 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          ∀ d ∈ digitsOf r.val, d ≠ 0 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            ∀ d ∈ digitsOf r.val, d ≠ 0) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, no decimal digit of r is 1.
    Preconditions: 2 <= num <= 2147483647. -/
  theorem spec_11 (num : Std.I64) (hnum_lo : 2 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          ∀ d ∈ digitsOf r.val, d ≠ 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 2 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            ∀ d ∈ digitsOf r.val, d ≠ 1) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, every decimal digit d of r divides num.
    Preconditions: 1 <= num <= 2147483647. Let D(z) be the product of the decimal digits of positive integer z. -/
  theorem spec_12 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          ∀ d ∈ digitsOf r.val, (d : Int) ∣ num.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            ∀ d ∈ digitsOf r.val, (d : Int) ∣ num.val) := by
    sorry

  /-- Whenever the function returns a result r with r != 0, r has at least two decimal digits.
    Preconditions: 10 <= num <= 2147483647. -/
  theorem spec_13 (num : Std.I64) (hnum_lo : 10 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 →
          2 ≤ (digitsOf r.val).length := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 10 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 →
            2 ≤ (digitsOf r.val).length) := by
    sorry

  /-- Whenever the function returns a result r with r != 0 and num is even, at least one decimal digit of r is even.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_14 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 → num.val % 2 = 0 →
          ∃ d, d ∈ digitsOf r.val ∧ d % 2 = 0 := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 → num.val % 2 = 0 →
            ∃ d, d ∈ digitsOf r.val ∧ d % 2 = 0) := by
    sorry

  /-- Whenever the function returns a result r with r != 0 and 5 divides num, at least one decimal digit of r is 5.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_15 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 → (5 : Int) ∣ num.val →
          ∃ d, d ∈ digitsOf r.val ∧ d = 5 := by
    sorry

  theorem spec_15_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 → (5 : Int) ∣ num.val →
            ∃ d, d ∈ digitsOf r.val ∧ d = 5) := by
    sorry

  /-- Whenever the function returns a result r with r != 0 and num is odd, every decimal digit of r is odd.
    Preconditions: 1 <= num <= 2147483647. -/
  theorem spec_16 (num : Std.I64) (hnum_lo : 1 ≤ num.val)
      (hnum_hi : num.val ≤ 2147483647) :
      ∀ r : Std.I64,
        smallest_factorization num = ok r → r.val ≠ 0 → num.val % 2 = 1 →
          ∀ d ∈ digitsOf r.val, d % 2 = 1 := by
    sorry

  theorem spec_16_neg :
      ¬ (∀ (num : Std.I64) (hnum_lo : 1 ≤ num.val)
        (hnum_hi : num.val ≤ 2147483647), ∀ r : Std.I64,
          smallest_factorization num = ok r → r.val ≠ 0 → num.val % 2 = 1 →
            ∀ d ∈ digitsOf r.val, d % 2 = 1) := by
    sorry

  end AegisSpec.SmallestFactorization
