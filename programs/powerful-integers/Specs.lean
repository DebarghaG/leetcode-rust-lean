import Aegis.PowerfulIntegers.Code.Funs

/-!
# Specifications of `Aegis.PowerfulIntegers.powerful_integers`

LeetCode problem `powerful-integers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.PowerfulIntegers

def Occurs (l : List Std.I64) (v : ℤ) : Prop := ∃ a ∈ l, a.val = v

def countVal (l : List Std.I64) (v : ℤ) : ℕ := (l.filter (fun a => a.val = v)).length

def IsPowerSum (x y v : ℤ) : Prop := ∃ i j : ℕ, x ^ i + y ^ j = v

def IsSingleVal (r : alloc.vec.Vec Std.I64) (v : ℤ) : Prop :=
  ∃ a : Std.I64, r.val = [a] ∧ a.val = v

/-- The function returns a result r and, for every integer v, the number of indices k with 0 <= k < len(r) and r[k] = v is 1 exactly when 2 <= v <= bound and there exist integers i >= 0 and j >= 0 such that x^i + y^j = v; that number is 0 otherwise. The elements of r may be in any order.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_1 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔ (2 ≤ v ∧ v ≤ bound.val ∧ IsPowerSum x.val y.val v)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ IsPowerSum x.val y.val v) → countVal r.val v = 0)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔ (2 ≤ v ∧ v ≤ bound.val ∧ IsPowerSum x.val y.val v)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ IsPowerSum x.val y.val v) → countVal r.val v = 0))) := by
  sorry

/-- Whenever the function returns a result r, for every index k with 0 <= k < len(r), there exist integers i >= 0 and j >= 0 such that r[k] = x^i + y^j.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_2 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k : ℕ) (hk : k < r.val.length), IsPowerSum x.val y.val (r.val[k]).val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k : ℕ) (hk : k < r.val.length), IsPowerSum x.val y.val (r.val[k]).val) := by
  sorry

/-- Whenever the function returns a result r, for every pair of integers i >= 0 and j >= 0 with x^i + y^j <= bound, the value x^i + y^j occurs in r, i.e. there exists k with 0 <= k < len(r) and r[k] = x^i + y^j.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_3 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (i j : ℕ), x.val ^ i + y.val ^ j ≤ bound.val →
        Occurs r.val (x.val ^ i + y.val ^ j) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (i j : ℕ), x.val ^ i + y.val ^ j ≤ bound.val →
        Occurs r.val (x.val ^ i + y.val ^ j)) := by
  sorry

/-- Whenever the function returns a result r, for every k and l with 0 <= k < len(r) and 0 <= l < len(r), if r[k] = r[l] then k = l.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_4 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k l : ℕ) (hk : k < r.val.length) (hl : l < r.val.length),
        r.val[k] = r.val[l] → k = l := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k l : ℕ) (hk : k < r.val.length) (hl : l < r.val.length),
        r.val[k] = r.val[l] → k = l) := by
  sorry

/-- Whenever the function returns a result r, for every index k with 0 <= k < len(r), 2 <= r[k] <= bound.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_5 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k : ℕ) (hk : k < r.val.length),
        2 ≤ (r.val[k]).val ∧ (r.val[k]).val ≤ bound.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      ∀ (k : ℕ) (hk : k < r.val.length),
        2 ≤ (r.val[k]).val ∧ (r.val[k]).val ≤ bound.val) := by
  sorry

/-- The function returns a result r; it does not fail, panic, or overflow for any input satisfying the preconditions.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_6 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r) := by
  sorry

/-- If bound < 2, then the function returns a result r and len(r) = 0.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_7 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : bound.val < 2) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ r.val.length = 0 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : bound.val < 2), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ r.val.length = 0) := by
  sorry

/-- If bound = 2, then the function returns a result r, len(r) = 1, and r[0] = 2.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_8 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : bound.val = 2) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ IsSingleVal r 2 := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : bound.val = 2), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ IsSingleVal r 2) := by
  sorry

/-- If x = 1 and y = 1, then the function returns a result r and: if bound >= 2 then len(r) = 1 and r[0] = 2; if bound < 2 then len(r) = 0.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_9 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hx : x.val = 1) (hy : y.val = 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      ((2 ≤ bound.val → IsSingleVal r 2) ∧ (bound.val < 2 → r.val.length = 0)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hx : x.val = 1) (hy : y.val = 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      ((2 ≤ bound.val → IsSingleVal r 2) ∧ (bound.val < 2 → r.val.length = 0))) := by
  sorry

/-- If x = 1, then the function returns a result r and, for every integer v, the number of indices k with 0 <= k < len(r) and r[k] = v is 1 exactly when 2 <= v <= bound and there exists an integer j >= 0 such that v = 1 + y^j; that number is 0 otherwise. The elements of r may be in any order.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_10 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hx : x.val = 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔
            (2 ≤ v ∧ v ≤ bound.val ∧ ∃ j : ℕ, v = 1 + y.val ^ j)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ ∃ j : ℕ, v = 1 + y.val ^ j) →
            countVal r.val v = 0)) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hx : x.val = 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔
            (2 ≤ v ∧ v ≤ bound.val ∧ ∃ j : ℕ, v = 1 + y.val ^ j)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ ∃ j : ℕ, v = 1 + y.val ^ j) →
            countVal r.val v = 0))) := by
  sorry

/-- If y = 1, then the function returns a result r and, for every integer v, the number of indices k with 0 <= k < len(r) and r[k] = v is 1 exactly when 2 <= v <= bound and there exists an integer i >= 0 such that v = x^i + 1; that number is 0 otherwise. The elements of r may be in any order.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_11 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hy : y.val = 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔
            (2 ≤ v ∧ v ≤ bound.val ∧ ∃ i : ℕ, v = x.val ^ i + 1)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ ∃ i : ℕ, v = x.val ^ i + 1) →
            countVal r.val v = 0)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hy : y.val = 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (∀ v : ℤ,
        (countVal r.val v = 1 ↔
            (2 ≤ v ∧ v ≤ bound.val ∧ ∃ i : ℕ, v = x.val ^ i + 1)) ∧
        (¬ (2 ≤ v ∧ v ≤ bound.val ∧ ∃ i : ℕ, v = x.val ^ i + 1) →
            countVal r.val v = 0))) := by
  sorry

/-- The function returns a result r, and the integer 2 occurs in r if and only if bound >= 2.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_12 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (Occurs r.val 2 ↔ 2 ≤ bound.val) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧
      (Occurs r.val 2 ↔ 2 ≤ bound.val)) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= max(0, bound - 1).
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_13 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      (r.val.length : ℤ) ≤ max 0 (bound.val - 1) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r →
      (r.val.length : ℤ) ≤ max 0 (bound.val - 1)) := by
  sorry

/-- If bound >= 2, x > bound - 1, and y > bound - 1, then the function returns a result r with len(r) = 1 and r[0] = 2.
  Preconditions: 1 <= x <= 100, 1 <= y <= 100, and 0 <= bound <= 1000000. -/
theorem spec_14 (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : 2 ≤ bound.val) (hx : bound.val - 1 < x.val) (hy : bound.val - 1 < y.val) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ IsSingleVal r 2 := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (x y bound : Std.I64)
    (hx_lo : 1 ≤ x.val) (hx_hi : x.val ≤ 100)
    (hy_lo : 1 ≤ y.val) (hy_hi : y.val ≤ 100)
    (hb_lo : 0 ≤ bound.val) (hb_hi : bound.val ≤ 1000000)
    (hb : 2 ≤ bound.val) (hx : bound.val - 1 < x.val) (hy : bound.val - 1 < y.val), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.PowerfulIntegers.powerful_integers x y bound = ok r ∧ IsSingleVal r 2) := by
  sorry

end AegisSpec.PowerfulIntegers
