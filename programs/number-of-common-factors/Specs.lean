import Aegis.CommonFactors.Code.Funs

/-!
# Specifications of `Aegis.CommonFactors.common_factors`

LeetCode problem `number-of-common-factors`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.CommonFactors

  def posDivisors (n : Int) : Finset Int :=
    ((Finset.Icc 1 n.toNat).image (fun d : Nat => (d : Int))).filter (fun d => d ∣ n)

  def numPositiveDivisors (n : Int) : Nat := (posDivisors n).card

  def numCommonDivisors (a b : Int) : Nat :=
    (((Finset.Icc 1 (min a b).toNat).image (fun d : Nat => (d : Int))).filter
      (fun d => d ∣ a ∧ d ∣ b)).card

  def intGcd (a b : Int) : Int := (Nat.gcd a.natAbs b.natAbs : Int)

  def isPrimeInt (p : Int) : Prop := 1 < p ∧ ∀ d : Int, 1 ≤ d → d ∣ p → d = 1 ∨ d = p

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is exactly the number of integers d such that 1 <= d <= min(a,b), d divides a, and d divides b. Here 'd divides x' means there exists an integer k with x = d*k, and min(a,b) uses the mathematical integer values of a and b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_1
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = Int.ofNat (numCommonDivisors a.val b.val) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = Int.ofNat (numCommonDivisors a.val b.val)) := by
    sorry

  /-- common_factors(a,b) returns a result; it does not fail with a panic, arithmetic overflow, out-of-bounds access, or any other failure.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_2
      (a b : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000) :
      ∃ r : Std.I64, Aegis.CommonFactors.common_factors a b = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (a b : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000), ∃ r : Std.I64, Aegis.CommonFactors.common_factors a b = ok r) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is at least 1.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_3
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is at most min(a,b).
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_4
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val ≤ min a.val b.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val ≤ min a.val b.val) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is at most the minimum of the number of positive divisors of a and the number of positive divisors of b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_5
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val ≤ Int.ofNat (min (numPositiveDivisors a.val) (numPositiveDivisors b.val)) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val ≤ Int.ofNat (min (numPositiveDivisors a.val) (numPositiveDivisors b.val))) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is at most 32.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_6
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val ≤ 32 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val ≤ 32) := by
    sorry

  /-- For every pair (a,b) satisfying the preconditions, if common_factors(a,b) returns r_ab and common_factors(b,a) returns r_ba, then the mathematical integer values of r_ab and r_ba are equal.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_7
      (a b r_ab r_ba : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h_ab : Aegis.CommonFactors.common_factors a b = ok r_ab)
      (h_ba : Aegis.CommonFactors.common_factors b a = ok r_ba) :
      r_ab.val = r_ba.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (a b r_ab r_ba : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h_ab : Aegis.CommonFactors.common_factors a b = ok r_ab)
        (h_ba : Aegis.CommonFactors.common_factors b a = ok r_ba), r_ab.val = r_ba.val) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r equals 1 if and only if gcd(a,b) = 1, where gcd(a,b) denotes the greatest positive integer that divides both a and b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_8
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = 1 ↔ intGcd a.val b.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = 1 ↔ intGcd a.val b.val = 1) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r equals the number of positive divisors of gcd(a,b), where gcd(a,b) denotes the greatest positive integer that divides both a and b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_9
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = Int.ofNat (numPositiveDivisors (intGcd a.val b.val)) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = Int.ofNat (numPositiveDivisors (intGcd a.val b.val))) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r equals the number of positive divisors of min(a,b).
    Preconditions: a and b are the i64 parameters of common_factors, 1 <= a <= 1000, 1 <= b <= 1000, and either a divides b or b divides a (there exists an integer k with b = a*k or a = b*k). -/
  theorem spec_10
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (hdvd : a.val ∣ b.val ∨ b.val ∣ a.val)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = Int.ofNat (numPositiveDivisors (min a.val b.val)) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (hdvd : a.val ∣ b.val ∨ b.val ∣ a.val)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = Int.ofNat (numPositiveDivisors (min a.val b.val))) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r equals 2 if a divides b, and equals 1 otherwise.
    Preconditions: a and b are the i64 parameters of common_factors, 1 <= a <= 1000, 1 <= b <= 1000, and a is prime (a > 1 and the only positive divisors of a are 1 and a). -/
  theorem spec_11
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (hp : isPrimeInt a.val)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = if a.val ∣ b.val then 2 else 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (hp : isPrimeInt a.val)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = if a.val ∣ b.val then 2 else 1) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is odd if and only if gcd(a,b) is a perfect square (there exists an integer s with gcd(a,b) = s*s), where gcd(a,b) denotes the greatest positive integer dividing both a and b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_12
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      Odd r.val ↔ ∃ s : Int, intGcd a.val b.val = s * s := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), Odd r.val ↔ ∃ s : Int, intGcd a.val b.val = s * s) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r equals 2 if and only if gcd(a,b) is prime (a positive integer greater than 1 whose only positive divisors are 1 and itself), where gcd(a,b) denotes the greatest positive integer dividing both a and b.
    Preconditions: a and b are the i64 parameters of common_factors, and their mathematical integer values satisfy 1 <= a <= 1000 and 1 <= b <= 1000. -/
  theorem spec_13
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      r.val = 2 ↔ isPrimeInt (intGcd a.val b.val) := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (h : Aegis.CommonFactors.common_factors a b = ok r), r.val = 2 ↔ isPrimeInt (intGcd a.val b.val)) := by
    sorry

  /-- Whenever common_factors(a,b) returns a result r, the mathematical integer value of r is at least 2.
    Preconditions: a and b are the i64 parameters of common_factors, 1 <= a <= 1000, 1 <= b <= 1000, and both a and b are even (there exist integers u,v with a = 2*u and b = 2*v). -/
  theorem spec_14
      (a b r : Std.I64)
      (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
      (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
      (hae : ∃ u : Int, a.val = 2 * u) (hbe : ∃ v : Int, b.val = 2 * v)
      (h : Aegis.CommonFactors.common_factors a b = ok r) :
      2 ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (a b r : Std.I64)
        (ha1 : 1 ≤ a.val) (ha2 : a.val ≤ 1000)
        (hb1 : 1 ≤ b.val) (hb2 : b.val ≤ 1000)
        (hae : ∃ u : Int, a.val = 2 * u) (hbe : ∃ v : Int, b.val = 2 * v)
        (h : Aegis.CommonFactors.common_factors a b = ok r), 2 ≤ r.val) := by
    sorry

  end AegisSpec.CommonFactors
