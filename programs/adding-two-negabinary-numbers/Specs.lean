import Aegis.AddNegabinary.Code.Funs

/-!
# Specifications of `Aegis.AddNegabinary.add_negabinary`

LeetCode problem `adding-two-negabinary-numbers`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.AddNegabinary

def digits (l : List Std.I64) : List Int := l.map (fun x => x.val)

def val (l : List Int) : Int :=
  ∑ i : Fin l.length, l.get i * (-2 : Int) ^ (l.length - 1 - (i : ℕ))

def arrayVal (l : List Std.I64) : Int := val (digits l)

/-- Whenever the function returns a result r, the following hold: (1) len(r) >= 1; (2) for every i with 0 <= i < len(r), r[i] is 0 or 1; (3) r = [0] or r[0] = 1; (4) val(r) = val(arr1) + val(arr2), where for any array a of length n, val(a) = sum_{i=0}^{n-1} a[i] * (-2)^(n-1-i).
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_1 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r) :
    1 ≤ r.val.length ∧
      (∀ d ∈ digits r.val, d = 0 ∨ d = 1) ∧
      (digits r.val = [0] ∨ (digits r.val).head? = some 1) ∧
      arrayVal r.val = arrayVal arr1.val + arrayVal arr2.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r), 1 ≤ r.val.length ∧
      (∀ d ∈ digits r.val, d = 0 ∨ d = 1) ∧
      (digits r.val = [0] ∨ (digits r.val).head? = some 1) ∧
      arrayVal r.val = arrayVal arr1.val + arrayVal arr2.val) := by
  sorry

/-- For every arr1 and arr2 satisfying the preconditions, the function returns a result r (it does not fail, panic, or overflow).
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_2 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r) := by
  sorry

/-- For every arr1 and arr2 satisfying the preconditions, let r1 be the result of add_negabinary(arr1, arr2) and r2 be the result of add_negabinary(arr2, arr1). Whenever both calls return (i.e., return results r1 and r2), r1 = r2.
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_3 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hres1 : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r1)
    (hres2 : Aegis.AddNegabinary.add_negabinary arr2 arr1 = ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r1 r2 : alloc.vec.Vec Std.I64)
    (hres1 : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r1)
    (hres2 : Aegis.AddNegabinary.add_negabinary arr2 arr1 = ok r2), r1.val = r2.val) := by
  sorry

/-- Whenever the function returns a result r, len(r) <= max(len(arr1), len(arr2)) + 2.
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_4 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r) :
    r.val.length ≤ max arr1.val.length arr2.val.length + 2 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r), r.val.length ≤ max arr1.val.length arr2.val.length + 2) := by
  sorry

/-- Whenever the function returns a result r, for every array b such that len(b) >= 1, every element of b is 0 or 1, b = [0] or b[0] = 1, and val(b) = val(arr1) + val(arr2), it holds that b = r.
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_5 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r)
    (b : Slice Std.I64)
    (hblen : 1 ≤ b.val.length)
    (hbdig : ∀ d ∈ digits b.val, d = 0 ∨ d = 1)
    (hbcanon : digits b.val = [0] ∨ (digits b.val).head? = some 1)
    (hbval : arrayVal b.val = arrayVal arr1.val + arrayVal arr2.val) :
    b.val = r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r)
    (b : Slice Std.I64)
    (hblen : 1 ≤ b.val.length)
    (hbdig : ∀ d ∈ digits b.val, d = 0 ∨ d = 1)
    (hbcanon : digits b.val = [0] ∨ (digits b.val).head? = some 1)
    (hbval : arrayVal b.val = arrayVal arr1.val + arrayVal arr2.val), b.val = r.val) := by
  sorry

/-- Whenever the function returns a result r, if val(arr1) + val(arr2) > 0 then len(r) is odd, and if val(arr1) + val(arr2) < 0 then len(r) is even.
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_6 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r) :
    (0 < arrayVal arr1.val + arrayVal arr2.val → Odd r.val.length) ∧
      (arrayVal arr1.val + arrayVal arr2.val < 0 → Even r.val.length) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r), (0 < arrayVal arr1.val + arrayVal arr2.val → Odd r.val.length) ∧
      (arrayVal arr1.val + arrayVal arr2.val < 0 → Even r.val.length)) := by
  sorry

/-- Whenever the function returns a result r, the least significant digit r[len(r)-1] is 0 if val(arr1) + val(arr2) is even, and is 1 if val(arr1) + val(arr2) is odd.
  Preconditions: arr1 and arr2 are valid negabinary arrays: 1 <= len(arr1) <= 1000, 1 <= len(arr2) <= 1000; for every i with 0 <= i < len(arr1), arr1[i] is 0 or 1; for every i with 0 <= i < len(arr2), arr2[i] is 0 or 1; arr1 = [0] or arr1[0] = 1; arr2 = [0] or arr2[0] = 1. -/
theorem spec_7 (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r) :
    (Even (arrayVal arr1.val + arrayVal arr2.val) → (digits r.val).getLast? = some 0) ∧
      (Odd (arrayVal arr1.val + arrayVal arr2.val) → (digits r.val).getLast? = some 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (arr1 arr2 : Slice Std.I64)
    (h1len : 1 ≤ arr1.val.length) (h1ub : arr1.val.length ≤ 1000)
    (h2len : 1 ≤ arr2.val.length) (h2ub : arr2.val.length ≤ 1000)
    (h1dig : ∀ d ∈ digits arr1.val, d = 0 ∨ d = 1)
    (h2dig : ∀ d ∈ digits arr2.val, d = 0 ∨ d = 1)
    (h1canon : digits arr1.val = [0] ∨ (digits arr1.val).head? = some 1)
    (h2canon : digits arr2.val = [0] ∨ (digits arr2.val).head? = some 1)
    (r : alloc.vec.Vec Std.I64)
    (hres : Aegis.AddNegabinary.add_negabinary arr1 arr2 = ok r), (Even (arrayVal arr1.val + arrayVal arr2.val) → (digits r.val).getLast? = some 0) ∧
      (Odd (arrayVal arr1.val + arrayVal arr2.val) → (digits r.val).getLast? = some 1)) := by
  sorry

end AegisSpec.AddNegabinary
