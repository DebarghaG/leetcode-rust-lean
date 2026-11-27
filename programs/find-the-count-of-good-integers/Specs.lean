import Aegis.CountGoodIntegers.Code.Funs

/-!
# Specifications of `Aegis.CountGoodIntegers.count_good_integers`

LeetCode problem `find-the-count-of-good-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  open Aegis.CountGoodIntegers

  namespace AegisSpec.CountGoodIntegers

  def natVal (x : I64) : Nat := x.val.toNat

  def digitsOf (x : Nat) : List Nat :=
    if x = 0 then [] else digitsOf (x / 10) ++ [x % 10]
  termination_by x
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

  def digitCount (x d : Nat) : Nat := (digitsOf x).count d

  def digitSum (x : Nat) : Nat := (digitsOf x).sum

  def firstDigit (x : Nat) : Nat := (digitsOf x).headD 0

  def lastDigit (x : Nat) : Nat := x % 10

  def HasNDigits (n x : Nat) : Prop := 10 ^ (n - 1) ≤ x ∧ x ≤ 10 ^ n - 1

  def IsPalindromicNat (x : Nat) : Prop := (digitsOf x).reverse = digitsOf x

  def SameDigits (x y : Nat) : Prop := ∀ d, digitCount x d = digitCount y d

  def IsPalindromicRearrangement (n x y : Nat) : Prop :=
    HasNDigits n y ∧ SameDigits x y ∧ IsPalindromicNat y

  def CanRearrangeIntoPalindrome (n x : Nat) : Prop :=
    ∃ y, IsPalindromicRearrangement n x y

  def CanRearrangeWithEnds (n x : Nat) (S : Finset Nat) : Prop :=
    ∃ y, IsPalindromicRearrangement n x y ∧ firstDigit y ∈ S ∧ lastDigit y ∈ S

  def Counted (n k x : Nat) : Prop :=
    HasNDigits n x ∧ ∃ y, IsPalindromicRearrangement n x y ∧ k ∣ y

  noncomputable def goodIntegers (n k : Nat) : Finset Nat :=
    @Finset.filter Nat (fun x => Counted n k x) (Classical.decPred _)
      (Finset.Icc (10 ^ (n - 1)) (10 ^ n - 1))

  noncomputable def oddDigitCount (x : Nat) : Nat :=
    (@Finset.filter Nat (fun d => digitCount x d % 2 = 1)
      (Classical.decPred _) (Finset.range 10)).card

  /-- Whenever count_good_integers(n,k) returns a result r, r is the number of integers x such that 10^(n-1) <= x <= 10^n - 1 and there exists an integer y such that: (i) y has exactly n decimal digits, i.e. 10^(n-1) <= y <= 10^n - 1; (ii) the multiset of decimal digits of y equals the multiset of decimal digits of x; (iii) y is a palindrome (its n decimal digits read the same forwards and backwards); and (iv) k divides y. Equivalently, r is the number of n-digit positive integers whose digits can be rearranged, without leading zero in the rearranged number, into an n-digit palindrome divisible by k. Each such integer x is counted once, no matter how many witness rearrangements y exist.
    Preconditions: n and k are the integer values of the parameters, with 1 <= n <= 10 and 1 <= k <= 9. -/
  theorem spec_1 (n k : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
      (r : I64) (hr : count_good_integers n k = ok r) :
      r.val = ((goodIntegers (natVal n) (natVal k)).card : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n k : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
        (r : I64) (hr : count_good_integers n k = ok r), r.val = ((goodIntegers (natVal n) (natVal k)).card : Int)) := by
    sorry

  /-- For every n and k satisfying the preconditions, count_good_integers(n,k) returns a result (it does not fail, panic, or overflow).
    Preconditions: n and k are the integer values of the parameters, with 1 <= n <= 10 and 1 <= k <= 9. -/
  theorem spec_2 (n k : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9) :
      ∃ r : I64, count_good_integers n k = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n k : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9), ∃ r : I64, count_good_integers n k = ok r) := by
    sorry

  /-- Whenever count_good_integers(n,k) returns a result r, one has 1 <= r <= 9 * 10^(n-1).
    Preconditions: n and k are the integer values of the parameters, with 1 <= n <= 10 and 1 <= k <= 9. -/
  theorem spec_3 (n k : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
      (r : I64) (hr : count_good_integers n k = ok r) :
      1 ≤ r.val ∧ r.val ≤ 9 * 10 ^ (natVal n - 1) := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n k : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
        (r : I64) (hr : count_good_integers n k = ok r), 1 ≤ r.val ∧ r.val ≤ 9 * 10 ^ (natVal n - 1)) := by
    sorry

  /-- When n = 1, if count_good_integers(1,k) returns r, then r is the number of d in {1,2,...,9} such that k divides d; equivalently r = floor(9/k).
    Preconditions: n and k are the integer values of the parameters, with n = 1 and 1 <= k <= 9. -/
  theorem spec_4 (n k : I64)
      (hn : n.val = 1)
      (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
      (r : I64) (hr : count_good_integers n k = ok r) :
      r.val = (((Finset.Icc 1 9).filter (fun d => natVal k ∣ d)).card : Int) ∧
        r.val = ((9 / natVal k : Nat) : Int) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n k : I64)
        (hn : n.val = 1)
        (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 9)
        (r : I64) (hr : count_good_integers n k = ok r), r.val = (((Finset.Icc 1 9).filter (fun d => natVal k ∣ d)).card : Int) ∧
          r.val = ((9 / natVal k : Nat) : Int)) := by
    sorry

  /-- Whenever count_good_integers(n,k1) returns r1 and count_good_integers(n,k2) returns r2, we have r2 <= r1.
    Preconditions: n, k1, and k2 are integers with 1 <= n <= 10, 1 <= k1 <= 9, 1 <= k2 <= 9, and k1 divides k2. -/
  theorem spec_5 (n k1 k2 : I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
      (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 9)
      (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 9)
      (hdiv : k1.val ∣ k2.val)
      (r1 r2 : I64)
      (hr1 : count_good_integers n k1 = ok r1)
      (hr2 : count_good_integers n k2 = ok r2) :
      r2.val ≤ r1.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n k1 k2 : I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 10)
        (hk1_lo : 1 ≤ k1.val) (hk1_hi : k1.val ≤ 9)
        (hk2_lo : 1 ≤ k2.val) (hk2_hi : k2.val ≤ 9)
        (hdiv : k1.val ∣ k2.val)
        (r1 r2 : I64)
        (hr1 : count_good_integers n k1 = ok r1)
        (hr2 : count_good_integers n k2 = ok r2), r2.val ≤ r1.val) := by
    sorry

  end AegisSpec.CountGoodIntegers
