import Aegis.NumberOfMatches.Code.Funs

/-!
# Specifications of `Aegis.NumberOfMatches.number_of_matches`

LeetCode problem `count-of-matches-in-tournament`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumberOfMatches

  /-- The function returns a result r and r = n - 1.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) :
      ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r ∧ r.val = n.val - 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200), ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r ∧ r.val = n.val - 1) := by
    sorry

  /-- The function does not fail: for every n in the range, there is an i64 result r such that the function returns r.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) :
      ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200), ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= 0.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_3 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
      (h : Aegis.NumberOfMatches.number_of_matches n = ok r) : 0 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
        (h : Aegis.NumberOfMatches.number_of_matches n = ok r), 0 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 199.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_4 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
      (h : Aegis.NumberOfMatches.number_of_matches n = ok r) : r.val ≤ 199 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
        (h : Aegis.NumberOfMatches.number_of_matches n = ok r), r.val ≤ 199) := by
    sorry

  /-- Whenever the function returns a result r, r < n.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_5 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
      (h : Aegis.NumberOfMatches.number_of_matches n = ok r) : r.val < n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
        (h : Aegis.NumberOfMatches.number_of_matches n = ok r), r.val < n.val) := by
    sorry

  /-- Whenever the function returns a result r, r and n have opposite parity; equivalently, r + n is odd.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_6 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
      (h : Aegis.NumberOfMatches.number_of_matches n = ok r) : Odd (r.val + n.val) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
        (h : Aegis.NumberOfMatches.number_of_matches n = ok r), Odd (r.val + n.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = 0 if and only if n = 1.
    Preconditions: 1 <= n <= 200. -/
  theorem spec_7 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
      (h : Aegis.NumberOfMatches.number_of_matches n = ok r) : r.val = 0 ↔ n.val = 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (r : Std.I64)
        (h : Aegis.NumberOfMatches.number_of_matches n = ok r), r.val = 0 ↔ n.val = 1) := by
    sorry

  /-- The function returns a result r and r >= 1.
    Preconditions: 1 <= n <= 200 and n > 1. -/
  theorem spec_8 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (hgt : 1 < n.val) :
      ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r ∧ 1 ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 200) (hgt : 1 < n.val), ∃ r : Std.I64, Aegis.NumberOfMatches.number_of_matches n = ok r ∧ 1 ≤ r.val) := by
    sorry

  /-- If the function returns r1 on input n1 and r2 on input n2, then n1 <= n2 implies r1 <= r2.
    Preconditions: 1 <= n1 <= 200 and 1 <= n2 <= 200. -/
  theorem spec_9 (n1 n2 : Std.I64) (hlo1 : 1 ≤ n1.val) (hhi1 : n1.val ≤ 200)
      (hlo2 : 1 ≤ n2.val) (hhi2 : n2.val ≤ 200) (r1 r2 : Std.I64)
      (h1 : Aegis.NumberOfMatches.number_of_matches n1 = ok r1)
      (h2 : Aegis.NumberOfMatches.number_of_matches n2 = ok r2)
      (hle : n1.val ≤ n2.val) : r1.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n1 n2 : Std.I64) (hlo1 : 1 ≤ n1.val) (hhi1 : n1.val ≤ 200)
        (hlo2 : 1 ≤ n2.val) (hhi2 : n2.val ≤ 200) (r1 r2 : Std.I64)
        (h1 : Aegis.NumberOfMatches.number_of_matches n1 = ok r1)
        (h2 : Aegis.NumberOfMatches.number_of_matches n2 = ok r2)
        (hle : n1.val ≤ n2.val), r1.val ≤ r2.val) := by
    sorry

  end AegisSpec.NumberOfMatches
