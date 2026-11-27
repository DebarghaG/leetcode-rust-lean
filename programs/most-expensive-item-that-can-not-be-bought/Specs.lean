import Aegis.MostExpensiveItem.Code.Funs

/-!
# Specifications of `Aegis.MostExpensiveItem.most_expensive_item`

LeetCode problem `most-expensive-item-that-can-not-be-bought`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MostExpensiveItem

  /-- The function returns a result r and r = primeOne * primeTwo - primeOne - primeTwo.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_1
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∃ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r ∧
          r.val = primeOne.val * primeTwo.val - primeOne.val - primeTwo.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∃ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r ∧
            r.val = primeOne.val * primeTwo.val - primeOne.val - primeTwo.val) := by
    sorry

  /-- The function returns a result r for every input satisfying the preconditions; it does not panic, overflow, or otherwise fail.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_2
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∃ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∃ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r < primeOne * primeTwo.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_3
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          1 ≤ r.val ∧ r.val < primeOne.val * primeTwo.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            1 ≤ r.val ∧ r.val < primeOne.val * primeTwo.val) := by
    sorry

  /-- Whenever the function returns a result r, there do not exist nonnegative integers a and b such that r = a * primeOne + b * primeTwo.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_4
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          ¬ ∃ a b : ℕ, r.val = (a : ℤ) * primeOne.val + (b : ℤ) * primeTwo.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            ¬ ∃ a b : ℕ, r.val = (a : ℤ) * primeOne.val + (b : ℤ) * primeTwo.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer x with r < x there exist nonnegative integers a and b such that x = a * primeOne + b * primeTwo.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_5
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          ∀ x : ℤ,
            r.val < x →
              ∃ a b : ℕ, x = (a : ℤ) * primeOne.val + (b : ℤ) * primeTwo.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            ∀ x : ℤ,
              r.val < x →
                ∃ a b : ℕ, x = (a : ℤ) * primeOne.val + (b : ℤ) * primeTwo.val) := by
    sorry

  /-- For any input satisfying the preconditions, if a call with parameters (primeOne, primeTwo) returns r and a call with parameters (primeTwo, primeOne) returns r', then r = r'.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_6
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r r' : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          Aegis.MostExpensiveItem.most_expensive_item primeTwo primeOne = ok r' →
            r = r' := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r r' : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            Aegis.MostExpensiveItem.most_expensive_item primeTwo primeOne = ok r' →
              r = r') := by
    sorry

  /-- Whenever the function returns a result r and either primeOne = 2 or primeTwo = 2, then r = (if primeOne = 2 then primeTwo else primeOne) - 2.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_7
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          (primeOne.val = 2 ∨ primeTwo.val = 2) →
            r.val = (if primeOne.val = 2 then primeTwo.val else primeOne.val) - 2 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            (primeOne.val = 2 ∨ primeTwo.val = 2) →
              r.val = (if primeOne.val = 2 then primeTwo.val else primeOne.val) - 2) := by
    sorry

  /-- Whenever the function returns a result r, r is odd.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_8
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          Odd r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            Odd r.val) := by
    sorry

  /-- Whenever the function returns a result r, primeOne does not divide r; that is, there is no integer k such that r = k * primeOne.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_9
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          ¬ ∃ k : ℤ, r.val = k * primeOne.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            ¬ ∃ k : ℤ, r.val = k * primeOne.val) := by
    sorry

  /-- Whenever the function returns a result r, primeTwo does not divide r; that is, there is no integer k such that r = k * primeTwo.
    Preconditions: primeOne and primeTwo are distinct prime integers, 1 < primeOne < 10000, 1 < primeTwo < 10000, and primeOne * primeTwo < 100000. -/
  theorem spec_10
      (primeOne primeTwo : Std.I64)
      (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
      (hne : primeOne.val ≠ primeTwo.val)
      (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
      (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
      (hprod : primeOne.val * primeTwo.val < 100000) :
      ∀ r : Std.I64,
        Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
          ¬ ∃ k : ℤ, r.val = k * primeTwo.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (primeOne primeTwo : Std.I64)
        (hprimeOne : Prime primeOne.val) (hprimeTwo : Prime primeTwo.val)
        (hne : primeOne.val ≠ primeTwo.val)
        (hgtOne : 1 < primeOne.val) (hgtTwo : 1 < primeTwo.val)
        (hltOne : primeOne.val < 10000) (hltTwo : primeTwo.val < 10000)
        (hprod : primeOne.val * primeTwo.val < 100000), ∀ r : Std.I64,
          Aegis.MostExpensiveItem.most_expensive_item primeOne primeTwo = ok r →
            ¬ ∃ k : ℤ, r.val = k * primeTwo.val) := by
    sorry

  end AegisSpec.MostExpensiveItem
