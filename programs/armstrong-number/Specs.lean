import Aegis.IsArmstrong.Code.Funs

/-!
# Specifications of `Aegis.IsArmstrong.is_armstrong`

LeetCode problem `armstrong-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  set_option autoImplicit false

  namespace AegisSpec.IsArmstrong

  def IsArmstrong (m : Nat) : Prop :=
    ∃ k : Nat, 1 ≤ k ∧ 10 ^ (k - 1) ≤ m ∧ m < 10 ^ k ∧
      m = ((List.range k).map (fun i => ((m / 10 ^ i) % 10) ^ k)).sum

  def numDigits (m : Nat) : Nat := if m = 0 then 0 else Nat.log 10 m + 1

  def knownArmstrongs : List Int :=
    [1, 2, 3, 4, 5, 6, 7, 8, 9,
      153, 370, 371, 407,
      1634, 8208, 9474,
      54748, 92727, 93084,
      548834,
      1741725, 4210818, 9800817, 9926315,
      24678050, 24678051, 88593477]

  /-- The function returns a result r and does not fail; moreover, r is true if and only if n is an Armstrong number. Here n is an Armstrong number exactly when, letting k be the unique positive integer with 10^(k-1) <= n < 10^k and defining d_i = (n / 10^i) mod 10 for 0 <= i < k using integer division, one has n = sum_{i=0}^{k-1} d_i^k. In particular, r is false exactly when this equality does not hold.
    Preconditions: 1 <= n <= 100000000. -/
  theorem spec_1 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000) :
      ∃ r : Bool, Aegis.IsArmstrong.is_armstrong n = ok r ∧
        (r = true ↔ IsArmstrong n.val.toNat) ∧
        (r = false ↔ ¬ IsArmstrong n.val.toNat) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000), ∃ r : Bool, Aegis.IsArmstrong.is_armstrong n = ok r ∧
          (r = true ↔ IsArmstrong n.val.toNat) ∧
          (r = false ↔ ¬ IsArmstrong n.val.toNat)) := by
    sorry

  /-- The function returns a result, either true or false, and does not fail through panic, arithmetic overflow, or out-of-bounds access.
    Preconditions: 1 <= n <= 100000000. -/
  theorem spec_2 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000) :
      ∃ r : Bool, Aegis.IsArmstrong.is_armstrong n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000), ∃ r : Bool, Aegis.IsArmstrong.is_armstrong n = ok r) := by
    sorry

  /-- The function returns true.
    Preconditions: 1 <= n <= 9. -/
  theorem spec_3 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 9) :
      Aegis.IsArmstrong.is_armstrong n = ok true := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 9), Aegis.IsArmstrong.is_armstrong n = ok true) := by
    sorry

  /-- The function returns false.
    Preconditions: There exists an integer k with 1 <= k <= 8 such that n = 10^k. -/
  theorem spec_4 (n : I64) (h : ∃ k : Nat, 1 ≤ k ∧ k ≤ 8 ∧ n.val = 10 ^ k) :
      Aegis.IsArmstrong.is_armstrong n = ok false := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : I64) (h : ∃ k : Nat, 1 ≤ k ∧ k ≤ 8 ∧ n.val = 10 ^ k), Aegis.IsArmstrong.is_armstrong n = ok false) := by
    sorry

  /-- Whenever the function returns true, n is one of the following integers: 1, 2, 3, 4, 5, 6, 7, 8, 9, 153, 370, 371, 407, 1634, 8208, 9474, 54748, 92727, 93084, 548834, 1741725, 4210818, 9800817, 9926315, 24678050, 24678051, 88593477.
    Preconditions: 1 <= n <= 100000000. -/
  theorem spec_5 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000) :
      Aegis.IsArmstrong.is_armstrong n = ok true → n.val ∈ knownArmstrongs := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000), Aegis.IsArmstrong.is_armstrong n = ok true → n.val ∈ knownArmstrongs) := by
    sorry

  /-- Whenever the function returns true, letting k be the number of decimal digits of n, one has n <= k * 9^k.
    Preconditions: 1 <= n <= 100000000. -/
  theorem spec_6 (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000) :
      Aegis.IsArmstrong.is_armstrong n = ok true →
        n.val ≤ (numDigits n.val.toNat : Int) * 9 ^ numDigits n.val.toNat := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 100000000), Aegis.IsArmstrong.is_armstrong n = ok true →
          n.val ≤ (numDigits n.val.toNat : Int) * 9 ^ numDigits n.val.toNat) := by
    sorry

  end AegisSpec.IsArmstrong
