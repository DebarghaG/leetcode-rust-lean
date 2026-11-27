import Aegis.RotatedDigits.Code.Funs

/-!
# Specifications of `Aegis.RotatedDigits.rotated_digits`

LeetCode problem `rotated-digits`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.RotatedDigits

  def digitsFuel : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, x => if x = 0 then [] else digitsFuel fuel (x / 10) ++ [x % 10]

  def digits (x : Nat) : List Nat := digitsFuel x x

  def ofDigits (l : List Nat) : Nat := l.foldl (fun acc d => acc * 10 + d) 0

  def rotDigit (d : Nat) : Nat :=
    match d with
    | 0 => 0
    | 1 => 1
    | 2 => 5
    | 5 => 2
    | 6 => 9
    | 8 => 8
    | 9 => 6
    | other => other

  def rotatedValue (x : Nat) : Nat := ofDigits ((digits x).map rotDigit)

  def rotatableDigits : List Nat := [0, 1, 2, 5, 6, 8, 9]

  def changingDigits : List Nat := [2, 5, 6, 9]

  def invariantDigits : List Nat := [0, 1, 8]

  def allDigitsIn (s : List Nat) (x : Nat) : Prop := ∀ d ∈ digits x, d ∈ s

  def someDigitIn (s : List Nat) (x : Nat) : Prop := ∃ d ∈ digits x, d ∈ s

  instance allDigitsIn.instDecidable (s : List Nat) (x : Nat) : Decidable (allDigitsIn s x) :=
    inferInstanceAs (Decidable (∀ d ∈ digits x, d ∈ s))

  instance someDigitIn.instDecidable (s : List Nat) (x : Nat) : Decidable (someDigitIn s x) :=
    inferInstanceAs (Decidable (∃ d ∈ digits x, d ∈ s))

  def digitsRotatable (x : Nat) : Prop := allDigitsIn rotatableDigits x

  def digitsInvariant (x : Nat) : Prop := allDigitsIn invariantDigits x

  def digitsChanging (x : Nat) : Prop := someDigitIn changingDigits x

  instance digitsRotatable.instDecidable (x : Nat) : Decidable (digitsRotatable x) :=
    inferInstanceAs (Decidable (allDigitsIn rotatableDigits x))

  instance digitsInvariant.instDecidable (x : Nat) : Decidable (digitsInvariant x) :=
    inferInstanceAs (Decidable (allDigitsIn invariantDigits x))

  instance digitsChanging.instDecidable (x : Nat) : Decidable (digitsChanging x) :=
    inferInstanceAs (Decidable (someDigitIn changingDigits x))

  def IsGood (x : Nat) : Prop := 1 ≤ x ∧ digitsRotatable x ∧ rotatedValue x ≠ x

  def IsGoodDigitwise (x : Nat) : Prop := digitsRotatable x ∧ digitsChanging x

  instance IsGood.instDecidable (x : Nat) : Decidable (IsGood x) :=
    inferInstanceAs (Decidable (1 ≤ x ∧ digitsRotatable x ∧ rotatedValue x ≠ x))

  instance IsGoodDigitwise.instDecidable (x : Nat) : Decidable (IsGoodDigitwise x) :=
    inferInstanceAs (Decidable (digitsRotatable x ∧ digitsChanging x))

  def countUpTo (p : Nat → Bool) : Nat → Nat
    | 0 => 0
    | N + 1 => countUpTo p N + (if p (N + 1) then 1 else 0)

  def goodCount (N : Nat) : Nat := countUpTo (fun x => decide (IsGood x)) N

  def rotatableCount (N : Nat) : Nat := countUpTo (fun x => decide (digitsRotatable x)) N

  def invariantCount (N : Nat) : Nat := countUpTo (fun x => decide (digitsInvariant x)) N

  def changingDigitsUpTo (N : Nat) : Nat :=
    (changingDigits.filter (fun d => decide (d ≤ N))).length

  /-- The function returns a result r and r equals the number of integers x such that 1 <= x <= n and x is good. For a positive integer x, write its decimal representation without leading zeros as the digit sequence a_0 a_1 ... a_{k-1}, where a_0 is the most significant digit. Then x is good if and only if: (1) every a_i belongs to {0,1,2,5,6,8,9}; and (2) with rot(0)=0, rot(1)=1, rot(2)=5, rot(5)=2, rot(6)=9, rot(8)=8, rot(9)=6, the digit sequence rot(a_0) rot(a_1) ... rot(a_{k-1}), kept in the same order with no reversal, denotes a decimal integer different from x.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_1 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∃ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r ∧
        r.val = (goodCount n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∃ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r ∧
          r.val = (goodCount n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs for any n satisfying the precondition.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_2 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∃ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∃ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 0 <= r <= n.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_3 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r → 0 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r → 0 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if n = 1.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_4 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r → (r.val = 0 ↔ n.val = 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r → (r.val = 0 ↔ n.val = 1)) := by
    sorry

  /-- Whenever the function returns a result r_n on input n and a result r_m on input m, r_n <= r_m.
    Preconditions: n and m are I64 values with 1 <= n <= m <= 10000. -/
  theorem spec_5 (n m : I64) (hn : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm : m.val ≤ 10000) :
      ∀ rn rm : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
        Aegis.RotatedDigits.rotated_digits m = ok rm → rn.val ≤ rm.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m : I64) (hn : 1 ≤ n.val) (hnm : n.val ≤ m.val) (hm : m.val ≤ 10000), ∀ rn rm : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
          Aegis.RotatedDigits.rotated_digits m = ok rm → rn.val ≤ rm.val) := by
    sorry

  /-- Whenever the function returns a result r_n on input n and a result r_{n+1} on input n+1, if n+1 is good (meaning every decimal digit of n+1 is in {0,1,2,5,6,8,9} and at least one decimal digit of n+1 is in {2,5,6,9}), then r_{n+1} = r_n + 1.
    Preconditions: n is an I64 value with 1 <= n < 10000. -/
  theorem spec_6 (n n1 : I64) (hlo : 1 ≤ n.val) (hhi : n.val < 10000) (hn1 : n1.val = n.val + 1) :
      ∀ rn rn1 : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
        Aegis.RotatedDigits.rotated_digits n1 = ok rn1 →
        IsGoodDigitwise n1.val.toNat → rn1.val = rn.val + 1 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n n1 : I64) (hlo : 1 ≤ n.val) (hhi : n.val < 10000) (hn1 : n1.val = n.val + 1), ∀ rn rn1 : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
          Aegis.RotatedDigits.rotated_digits n1 = ok rn1 →
          IsGoodDigitwise n1.val.toNat → rn1.val = rn.val + 1) := by
    sorry

  /-- Whenever the function returns a result r_n on input n and a result r_{n+1} on input n+1, if n+1 is not good (meaning either some decimal digit of n+1 is outside {0,1,2,5,6,8,9}, or no decimal digit of n+1 is in {2,5,6,9}), then r_{n+1} = r_n.
    Preconditions: n is an I64 value with 1 <= n < 10000. -/
  theorem spec_7 (n n1 : I64) (hlo : 1 ≤ n.val) (hhi : n.val < 10000) (hn1 : n1.val = n.val + 1) :
      ∀ rn rn1 : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
        Aegis.RotatedDigits.rotated_digits n1 = ok rn1 →
        ¬ IsGoodDigitwise n1.val.toNat → rn1.val = rn.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n n1 : I64) (hlo : 1 ≤ n.val) (hhi : n.val < 10000) (hn1 : n1.val = n.val + 1), ∀ rn rn1 : I64, Aegis.RotatedDigits.rotated_digits n = ok rn →
          Aegis.RotatedDigits.rotated_digits n1 = ok rn1 →
          ¬ IsGoodDigitwise n1.val.toNat → rn1.val = rn.val) := by
    sorry

  /-- Whenever the function returns a result r, r > 0 if and only if there exists an integer x with 1 <= x <= n such that x is good (every decimal digit of x is in {0,1,2,5,6,8,9} and at least one decimal digit of x is in {2,5,6,9}).
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_8 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
        (0 < r.val ↔ ∃ x : Nat, 1 ≤ x ∧ x ≤ n.val.toNat ∧ IsGoodDigitwise x) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
          (0 < r.val ↔ ∃ x : Nat, 1 ≤ x ∧ x ≤ n.val.toNat ∧ IsGoodDigitwise x)) := by
    sorry

  /-- Whenever the function returns a result r, r is at least the number of elements of the set {2,5,6,9} that are less than or equal to n.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_9 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
        (changingDigitsUpTo n.val.toNat : Int) ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
          (changingDigitsUpTo n.val.toNat : Int) ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r = A(n) - B(n), where A(n) is the number of integers x with 1 <= x <= n whose decimal digits all belong to {0,1,2,5,6,8,9}, and B(n) is the number of integers x with 1 <= x <= n whose decimal digits all belong to {0,1,8}.
    Preconditions: n is an I64 value with 1 <= n <= 10000. -/
  theorem spec_10 (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000) :
      ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
        r.val = (rotatableCount n.val.toNat : Int) - (invariantCount n.val.toNat : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 10000), ∀ r : I64, Aegis.RotatedDigits.rotated_digits n = ok r →
          r.val = (rotatableCount n.val.toNat : Int) - (invariantCount n.val.toNat : Int)) := by
    sorry

  end AegisSpec.RotatedDigits
