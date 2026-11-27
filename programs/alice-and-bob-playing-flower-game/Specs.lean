import Aegis.FlowerGame.Code.Funs

/-!
# Specifications of `Aegis.FlowerGame.flower_game`

LeetCode problem `alice-and-bob-playing-flower-game`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.FlowerGame

namespace AegisSpec.FlowerGame

def intOneTo (n : ℤ) : Finset ℤ :=
  (Finset.range n.toNat).image (fun k : ℕ => (k : ℤ) + 1)

def oddPairs (n m : ℤ) : Finset (ℤ × ℤ) :=
  ((intOneTo n) ×ˢ (intOneTo m)).filter (fun p => Odd (p.1 + p.2))

def countOddPairs (n m : ℤ) : ℕ := (oddPairs n m).card

def intToI64 (x : ℤ) (h0 : 0 ≤ x) (hle : x ≤ 100000) : Aeneas.Std.I64 :=
  Aeneas.Std.IScalar.ofInt x (by
    have hmin : Aeneas.Std.IScalar.cMin Aeneas.Std.IScalarTy.I64 = -(2 ^ 63) := by
      decide
    have hmax : Aeneas.Std.IScalar.cMax Aeneas.Std.IScalarTy.I64 = 2 ^ 63 - 1 := by
      decide
    omega)

/-- Let C be the number of ordered pairs (x, y) of integers such that 1 <= x <= n, 1 <= y <= m, and x + y is odd. The function returns a result r and r = C.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_1 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = (countOddPairs n.val m.val : ℤ) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = (countOddPairs n.val m.val : ℤ)) := by
  sorry

/-- The function returns a result r; it does not fail (no overflow, out-of-bounds access, panic, or other error) for any inputs satisfying the preconditions.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_2 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∃ r : Aeneas.Std.I64, flower_game n m = ok r) := by
  sorry

/-- The function returns a result r and r = floor((n * m) / 2), where floor denotes integer division by 2 with the remainder discarded.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_3 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val * m.val / 2 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val * m.val / 2) := by
  sorry

/-- The function returns a result r and 0 <= r <= floor((n * m) / 2), where floor denotes integer division by 2 with the remainder discarded.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_4 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ 0 ≤ r.val ∧ r.val ≤ n.val * m.val / 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ 0 ≤ r.val ∧ r.val ≤ n.val * m.val / 2) := by
  sorry

/-- Whenever the call flower_game(n, m) returns r and the call flower_game(m, n) returns s, we have r = s.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_5 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r → flower_game m n = ok s → r.val = s.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r → flower_game m n = ok s → r.val = s.val) := by
  sorry

/-- The function returns a result r, and r = 0 if and only if n = 1 and m = 1.
  Preconditions: n and m are the integer values of the parameters, with 1 <= n <= 100000 and 1 <= m <= 100000. -/
theorem spec_6 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ (r.val = 0 ↔ n.val = 1 ∧ m.val = 1) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ (r.val = 0 ↔ n.val = 1 ∧ m.val = 1)) := by
  sorry

/-- The function returns a result r and r = floor(m / 2), where floor denotes integer division by 2 with the remainder discarded.
  Preconditions: 1 <= m <= 100000 and n = 1. -/
theorem spec_7 (n m : Aeneas.Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn : n.val = 1) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = m.val / 2 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hn : n.val = 1), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = m.val / 2) := by
  sorry

/-- The function returns a result r and r = floor(n / 2), where floor denotes integer division by 2 with the remainder discarded.
  Preconditions: 1 <= n <= 100000 and m = 1. -/
theorem spec_8 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm : m.val = 1) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val / 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm : m.val = 1), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val / 2) := by
  sorry

/-- The function returns a result r and r = (n * m) / 2, with exact integer division.
  Preconditions: 1 <= n <= 100000, 1 <= m <= 100000, n is even, and m is even. -/
theorem spec_9 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hnEven : Even n.val) (hmEven : Even m.val) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val * m.val / 2 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hnEven : Even n.val) (hmEven : Even m.val), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = n.val * m.val / 2) := by
  sorry

/-- The function returns a result r and r = (n * m - 1) / 2, with exact integer division.
  Preconditions: 1 <= n <= 100000, 1 <= m <= 100000, n is odd, and m is odd. -/
theorem spec_10 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hnOdd : Odd n.val) (hmOdd : Odd m.val) :
    ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = (n.val * m.val - 1) / 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000)
    (hnOdd : Odd n.val) (hmOdd : Odd m.val), ∃ r : Aeneas.Std.I64, flower_game n m = ok r ∧ r.val = (n.val * m.val - 1) / 2) := by
  sorry

/-- Whenever flower_game(n, m) returns r and flower_game(n + 2, m) returns s, we have s = r + m.
  Preconditions: 1 <= n <= 99998 and 1 <= m <= 100000. -/
theorem spec_11 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 99998)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r →
      flower_game (intToI64 (n.val + 2) (by omega) (by omega)) m = ok s →
      s.val = r.val + m.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 99998)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r →
      flower_game (intToI64 (n.val + 2) (by omega) (by omega)) m = ok s →
      s.val = r.val + m.val) := by
  sorry

/-- Whenever flower_game(n, m) returns r and flower_game(n, m + 2) returns s, we have s = r + n.
  Preconditions: 1 <= n <= 100000 and 1 <= m <= 99998. -/
theorem spec_12 (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 99998) :
    ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r →
      flower_game n (intToI64 (m.val + 2) (by omega) (by omega)) = ok s →
      s.val = r.val + n.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 99998), ∀ r s : Aeneas.Std.I64,
      flower_game n m = ok r →
      flower_game n (intToI64 (m.val + 2) (by omega) (by omega)) = ok s →
      s.val = r.val + n.val) := by
  sorry

/-- Whenever flower_game(n1, m) returns r1 and flower_game(n2, m) returns r2, we have r1 <= r2.
  Preconditions: 1 <= n1 <= n2 <= 100000 and 1 <= m <= 100000. -/
theorem spec_13 (n1 n2 m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2 : n2.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000) :
    ∀ r1 r2 : Aeneas.Std.I64,
      flower_game n1 m = ok r1 → flower_game n2 m = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n1 n2 m : Aeneas.Std.I64)
    (hn1 : 1 ≤ n1.val) (hn12 : n1.val ≤ n2.val) (hn2 : n2.val ≤ 100000)
    (hm1 : 1 ≤ m.val) (hm2 : m.val ≤ 100000), ∀ r1 r2 : Aeneas.Std.I64,
      flower_game n1 m = ok r1 → flower_game n2 m = ok r2 → r1.val ≤ r2.val) := by
  sorry

/-- Whenever flower_game(n, m1) returns r1 and flower_game(n, m2) returns r2, we have r1 <= r2.
  Preconditions: 1 <= n <= 100000 and 1 <= m1 <= m2 <= 100000. -/
theorem spec_14 (n m1 m2 : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2 : m2.val ≤ 100000) :
    ∀ r1 r2 : Aeneas.Std.I64,
      flower_game n m1 = ok r1 → flower_game n m2 = ok r2 → r1.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n m1 m2 : Aeneas.Std.I64)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 100000)
    (hm1 : 1 ≤ m1.val) (hm12 : m1.val ≤ m2.val) (hm2 : m2.val ≤ 100000), ∀ r1 r2 : Aeneas.Std.I64,
      flower_game n m1 = ok r1 → flower_game n m2 = ok r2 → r1.val ≤ r2.val) := by
  sorry

end AegisSpec.FlowerGame
