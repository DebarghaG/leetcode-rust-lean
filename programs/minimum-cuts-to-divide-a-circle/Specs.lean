import Aegis.NumberOfCuts.Code.Funs

/-!
# Specifications of `Aegis.NumberOfCuts.number_of_cuts`

LeetCode problem `minimum-cuts-to-divide-a-circle`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfCuts

  /-- The function returns a result r and the value r is exactly: r = 0 if n = 1; r = n/2 if n is even (n mod 2 = 0); r = n if n is odd and n > 1 (n mod 2 = 1). Here n/2 is the exact integer quotient for even n.
    Preconditions: n is the integer value of the Std.I64 argument, and 1 <= n <= 100. -/
  theorem spec_1 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧
        ((n.val = 1 ∧ r.val = 0) ∨
         (n.val % 2 = 0 ∧ r.val = n.val / 2) ∨
         (n.val % 2 = 1 ∧ 1 < n.val ∧ r.val = n.val)) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧
          ((n.val = 1 ∧ r.val = 0) ∨
           (n.val % 2 = 0 ∧ r.val = n.val / 2) ∨
           (n.val % 2 = 1 ∧ 1 < n.val ∧ r.val = n.val))) := by
    sorry

  /-- The function returns some result r; it does not fail for any n satisfying the precondition.
    Preconditions: n is the integer value of the Std.I64 argument, and 1 <= n <= 100. -/
  theorem spec_2 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r) := by
    sorry

  /-- The function returns a result r and 0 <= r <= n.
    Preconditions: n is the integer value of the Std.I64 argument, and 1 <= n <= 100. -/
  theorem spec_3 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ 0 ≤ r.val ∧ r.val ≤ n.val) := by
    sorry

  /-- The function returns a result r, and r = 0 if and only if n = 1.
    Preconditions: n is the integer value of the Std.I64 argument, and 1 <= n <= 100. -/
  theorem spec_4 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = 0 ↔ n.val = 1) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = 0 ↔ n.val = 1)) := by
    sorry

  /-- The function returns a result r, and r = 1 if and only if n = 2.
    Preconditions: n is the integer value of the Std.I64 argument, and 1 <= n <= 100. -/
  theorem spec_5 (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = 1 ↔ n.val = 2) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = 1 ↔ n.val = 2)) := by
    sorry

  /-- The function returns a result r, and 2*r = n if and only if n is even.
    Preconditions: n is the integer value of the Std.I64 argument, and 2 <= n <= 100. -/
  theorem spec_6 (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (2 * r.val = n.val ↔ n.val % 2 = 0) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (2 * r.val = n.val ↔ n.val % 2 = 0)) := by
    sorry

  /-- The function returns a result r, and r = n if and only if n is odd.
    Preconditions: n is the integer value of the Std.I64 argument, and 2 <= n <= 100. -/
  theorem spec_7 (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = n.val ↔ n.val % 2 = 1) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (r.val = n.val ↔ n.val % 2 = 1)) := by
    sorry

  /-- The function returns a result r, and either n = r or n = 2*r.
    Preconditions: n is the integer value of the Std.I64 argument, and 2 <= n <= 100. -/
  theorem spec_8 (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (n.val = r.val ∨ n.val = 2 * r.val) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ (n.val = r.val ∨ n.val = 2 * r.val)) := by
    sorry

  /-- The function returns a result r, and r >= 2.
    Preconditions: n is the integer value of the Std.I64 argument, and 3 <= n <= 100. -/
  theorem spec_9 (n : Std.I64) (h_lo : 3 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ 2 ≤ r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 3 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ 2 ≤ r.val) := by
    sorry

  /-- The function returns a result r, and r < n.
    Preconditions: n is the integer value of the Std.I64 argument, 2 <= n <= 100, and n is even. -/
  theorem spec_10 (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) (h_even : n.val % 2 = 0) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ r.val < n.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) (h_even : n.val % 2 = 0), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ r.val < n.val) := by
    sorry

  /-- The function returns a result r, and r is odd (r mod 2 = 1).
    Preconditions: n is the integer value of the Std.I64 argument, 1 < n <= 100, and n is odd. -/
  theorem spec_11 (n : Std.I64) (h_lo : 1 < n.val) (h_hi : n.val ≤ 100) (h_odd : n.val % 2 = 1) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ r.val % 2 = 1 := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 1 < n.val) (h_hi : n.val ≤ 100) (h_odd : n.val % 2 = 1), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ r.val % 2 = 1) := by
    sorry

  /-- The function returns a result r, and 2*r >= n.
    Preconditions: n is the integer value of the Std.I64 argument, and 2 <= n <= 100. -/
  theorem spec_12 (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100) :
      ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ n.val ≤ 2 * r.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (n : Std.I64) (h_lo : 2 ≤ n.val) (h_hi : n.val ≤ 100), ∃ r, Aegis.NumberOfCuts.number_of_cuts n = ok r ∧ n.val ≤ 2 * r.val) := by
    sorry

  end AegisSpec.NumberOfCuts
