import Aegis.SmallestNumber.Code.Funs

/-!
# Specifications of `Aegis.SmallestNumber.smallest_number`

LeetCode problem `smallest-divisible-digit-product-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.SmallestNumber

namespace AegisSpec.SmallestNumber

def digitsAux : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, x => if x = 0 then [] else (x % 10) :: digitsAux fuel (x / 10)

def decimalDigits (x : Nat) : List Nat :=
  if x = 0 then [0] else digitsAux (x + 1) x

def digitProdNat (x : Nat) : Nat := (decimalDigits x).prod

def digProd (m : Int) : Int := if 0 ≤ m then ((digitProdNat m.toNat : Nat) : Int) else 0

def leastMultipleOfTen (n : Int) : Int := ((n + 9) / 10) * 10

/-- Let digprod(x) be the product of the digits in the usual decimal representation (no leading zeros) of a positive integer x. The function returns a result r and does not fail, and r is the least integer m such that m >= n and t divides digprod(m). Equivalently: r >= n; t divides digprod(r); and for every integer m with n <= m < r, t does not divide digprod(m).
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10, interpreting the Std.I64 parameters as mathematical integers. -/
theorem spec_1 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∃ r : I64, smallest_number n t = ok r ∧ n.val ≤ r.val ∧ t.val ∣ digProd r.val ∧
      ∀ m : Int, n.val ≤ m → m < r.val → ¬ (t.val ∣ digProd m) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∃ r : I64, smallest_number n t = ok r ∧ n.val ≤ r.val ∧ t.val ∣ digProd r.val ∧
      ∀ m : Int, n.val ≤ m → m < r.val → ¬ (t.val ∣ digProd m)) := by
  sorry

/-- The function returns a result r for every input satisfying the preconditions; it does not fail, overflow, or panic.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_2 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∃ r : I64, smallest_number n t = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∃ r : I64, smallest_number n t = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= n.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_3 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r → n.val ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r → n.val ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= 100.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_4 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r → r.val ≤ 100 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r → r.val ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, t divides the product of the decimal digits of r, where the usual decimal representation has no leading zeros and any zero digit makes the product 0.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_5 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r → t.val ∣ digProd r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r → t.val ∣ digProd r.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer m with n <= m < r, t does not divide the product of the decimal digits of m.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_6 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r →
      ∀ m : Int, n.val ≤ m → m < r.val → ¬ (t.val ∣ digProd m) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r →
      ∀ m : Int, n.val ≤ m → m < r.val → ¬ (t.val ∣ digProd m)) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if t divides the product of the decimal digits of n.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_7 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r → (r.val = n.val ↔ t.val ∣ digProd n.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r → (r.val = n.val ↔ t.val ∣ digProd n.val)) := by
  sorry

/-- Whenever the function returns a result r, r = 100 if and only if for every integer m with n <= m < 100, t does not divide the product of the decimal digits of m.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_8 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r →
      (r.val = 100 ↔ ∀ m : Int, n.val ≤ m → m < 100 → ¬ (t.val ∣ digProd m)) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r →
      (r.val = 100 ↔ ∀ m : Int, n.val ≤ m → m < 100 → ¬ (t.val ∣ digProd m))) := by
  sorry

/-- If the function returns r1 for input (n1, t) and returns r2 for input (n2, t), then r1 <= r2.
  Preconditions: 1 <= n1 <= n2 <= 100 and 1 <= t <= 10. -/
theorem spec_9 (n1 n2 t : I64) (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 100)
    (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r1 r2 : I64, smallest_number n1 t = ok r1 → smallest_number n2 t = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n1 n2 t : I64) (hn : 1 ≤ n1.val ∧ n1.val ≤ n2.val ∧ n2.val ≤ 100)
    (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r1 r2 : I64, smallest_number n1 t = ok r1 → smallest_number n2 t = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 for input (n, t1) and returns r2 for input (n, t2), then r1 <= r2.
  Preconditions: 1 <= n <= 100, 1 <= t1 <= 10, 1 <= t2 <= 10, and t1 divides t2. -/
theorem spec_10 (n t1 t2 : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (ht1 : 1 ≤ t1.val ∧ t1.val ≤ 10) (ht2 : 1 ≤ t2.val ∧ t2.val ≤ 10)
    (hdiv : t1.val ∣ t2.val) :
    ∀ r1 r2 : I64, smallest_number n t1 = ok r1 → smallest_number n t2 = ok r2 →
      r1.val ≤ r2.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n t1 t2 : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100)
    (ht1 : 1 ≤ t1.val ∧ t1.val ≤ 10) (ht2 : 1 ≤ t2.val ∧ t2.val ≤ 10)
    (hdiv : t1.val ∣ t2.val), ∀ r1 r2 : I64, smallest_number n t1 = ok r1 → smallest_number n t2 = ok r2 →
      r1.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns a result r, if q is the least multiple of 10 with q >= n, then r <= q.
  Preconditions: 1 <= n <= 100 and 1 <= t <= 10. -/
theorem spec_11 (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10) :
    ∀ r : I64, smallest_number n t = ok r → r.val ≤ leastMultipleOfTen n.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n t : I64) (hn : 1 ≤ n.val ∧ n.val ≤ 100) (ht : 1 ≤ t.val ∧ t.val ≤ 10), ∀ r : I64, smallest_number n t = ok r → r.val ≤ leastMultipleOfTen n.val) := by
  sorry

end AegisSpec.SmallestNumber
