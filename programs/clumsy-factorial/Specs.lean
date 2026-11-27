import Aegis.Clumsy.Code.Funs

/-!
# Specifications of `Aegis.Clumsy.clumsy`

LeetCode problem `clumsy-factorial`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.Clumsy

def aVal (n : ℤ) (i : ℤ) : ℤ := n - i

def floorDiv (x y : ℤ) : ℤ := x / y

def Bval (n : ℤ) : ℤ :=
  if n = 1 then aVal n 0
  else if n = 2 then aVal n 0 * aVal n 1
  else floorDiv (aVal n 0 * aVal n 1) (aVal n 2)

def Cval (n : ℤ) (k : ℕ) : ℤ :=
  if 4 * (k : ℤ) + 6 ≤ n - 1 then
    floorDiv (aVal n (4 * (k : ℤ) + 4) * aVal n (4 * (k : ℤ) + 5)) (aVal n (4 * (k : ℤ) + 6))
  else if 4 * (k : ℤ) + 5 ≤ n - 1 then
    aVal n (4 * (k : ℤ) + 4) * aVal n (4 * (k : ℤ) + 5)
  else
    aVal n (4 * (k : ℤ) + 4)

def specVal (n : ℤ) : ℤ :=
  Bval n
    + ((Finset.range (n - 1).toNat).filter (fun k : ℕ => 4 * (k : ℤ) + 3 ≤ n - 1)).sum
        (fun k : ℕ => aVal n (4 * (k : ℤ) + 3))
    - ((Finset.range (n - 1).toNat).filter (fun k : ℕ => 4 * (k : ℤ) + 4 ≤ n - 1)).sum
        (fun k : ℕ => Cval n k)

def i64OfInt (x : ℤ) (hlo : -9223372036854775808 ≤ x) (hhi : x ≤ 9223372036854775807) : Std.I64 :=
  Std.I64.ofInt x (by
    have h1 : Std.IScalar.cMin Std.IScalarTy.I64 = -9223372036854775808 := by decide
    have h2 : Std.IScalar.cMax Std.IScalarTy.I64 = 9223372036854775807 := by decide
    rw [h1, h2]
    exact ⟨hlo, hhi⟩)

/-- Whenever `clumsy n` returns a result `r`, its integer value is as follows. Put a_i = n - i for i = 0,...,n-1. Let B = a_0 if n=1, B = a_0*a_1 if n=2, and B = floor(a_0*a_1/a_2) if n >= 3. For each k >= 0 with 4k+3 <= n-1, add the term a_{4k+3}. For each k >= 0 with 4k+4 <= n-1, subtract C_k, where C_k = floor(a_{4k+4}*a_{4k+5}/a_{4k+6}) if 4k+6 <= n-1; C_k = a_{4k+4}*a_{4k+5} if 4k+5 <= n-1 < 4k+6; and C_k = a_{4k+4} if 4k+4 <= n-1 < 4k+5. Here floor(x/y) is the greatest integer <= x/y. Then r = B + (sum of all added terms) - (sum of all C_k).
  Preconditions: n is an integer with 1 ≤ n ≤ 10000. -/
theorem spec_1 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = specVal n.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = specVal n.val) := by
  sorry

/-- For every integer n with 1 ≤ n ≤ 10000, `clumsy n` returns a result r; it does not overflow, divide by zero, or panic.
  Preconditions: n is an integer with 1 ≤ n ≤ 10000. -/
theorem spec_2 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∃ r, Aegis.Clumsy.clumsy n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∃ r, Aegis.Clumsy.clumsy n = ok r) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r > 0.
  Preconditions: n is an integer with 1 ≤ n ≤ 10000. -/
theorem spec_3 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → 0 < r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.Clumsy.clumsy n = ok r → 0 < r.val) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r ≤ n + 3.
  Preconditions: n is an integer with 1 ≤ n ≤ 10000. -/
theorem spec_4 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val ≤ n.val + 3 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val ≤ n.val + 3) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r ≥ n - 1.
  Preconditions: n is an integer with 5 ≤ n ≤ 10000. -/
theorem spec_5 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → n.val - 1 ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.Clumsy.clumsy n = ok r → n.val - 1 ≤ r.val) := by
  sorry

/-- Whenever `clumsy n` returns a result r, the difference r - n belongs to the set {-1, 1, 2}.
  Preconditions: n is an integer with 5 ≤ n ≤ 10000. -/
theorem spec_6 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val - n.val ∈ ({-1, 1, 2} : Set ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val - n.val ∈ ({-1, 1, 2} : Set ℤ)) := by
  sorry

/-- Whenever `clumsy n` returns r and `clumsy (n+4)` returns s, we have s = r + 4.
  Preconditions: n is an integer with 5 ≤ n ≤ 9996. -/
theorem spec_7 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 9996) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r →
      ∀ s, Aegis.Clumsy.clumsy (i64OfInt (n.val + 4) (by omega) (by omega)) = ok s →
        s.val = r.val + 4 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 9996), ∀ r, Aegis.Clumsy.clumsy n = ok r →
      ∀ s, Aegis.Clumsy.clumsy (i64OfInt (n.val + 4) (by omega) (by omega)) = ok s →
        s.val = r.val + 4) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r is 1 when n=1, 2 when n=2, 6 when n=3, and 7 when n=4.
  Preconditions: n is an integer with 1 ≤ n ≤ 4. -/
theorem spec_8 (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 4) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r →
      (n.val = 1 → r.val = 1) ∧ (n.val = 2 → r.val = 2) ∧
        (n.val = 3 → r.val = 6) ∧ (n.val = 4 → r.val = 7) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 4), ∀ r, Aegis.Clumsy.clumsy n = ok r →
      (n.val = 1 → r.val = 1) ∧ (n.val = 2 → r.val = 2) ∧
        (n.val = 3 → r.val = 6) ∧ (n.val = 4 → r.val = 7)) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r = n + 1.
  Preconditions: n is an integer with 8 ≤ n ≤ 10000 and n mod 4 = 0. -/
theorem spec_9 (n : Std.I64) (hn1 : 8 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 0) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val + 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 8 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 0), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val + 1) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r = n + 2.
  Preconditions: n is an integer with 5 ≤ n ≤ 10000 and n mod 4 = 1. -/
theorem spec_10 (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 1) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val + 2 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 5 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 1), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val + 2) := by
  sorry

/-- Whenever `clumsy n` returns a result r, r = n - 1.
  Preconditions: n is an integer with 7 ≤ n ≤ 10000 and n mod 4 = 3. -/
theorem spec_11 (n : Std.I64) (hn1 : 7 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 3) :
    ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val - 1 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (hn1 : 7 ≤ n.val) (hn2 : n.val ≤ 10000) (hmod : n.val % 4 = 3), ∀ r, Aegis.Clumsy.clumsy n = ok r → r.val = n.val - 1) := by
  sorry

end AegisSpec.Clumsy
