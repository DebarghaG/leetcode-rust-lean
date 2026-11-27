import Aegis.IsFascinating.Code.Funs

/-!
# Specifications of `Aegis.IsFascinating.is_fascinating`

LeetCode problem `check-if-the-number-is-fascinating`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.IsFascinating (is_fascinating)

namespace AegisSpec.IsFascinating

def decDigitsRev (m : Nat) : List Nat :=
  if h : m = 0 then [] else (m % 10) :: decDigitsRev (m / 10)
termination_by m
decreasing_by
  have hpos : 0 < m := Nat.pos_of_ne_zero h
  omega

def decDigits (m : Nat) : List Nat := (decDigitsRev m).reverse

def fascinatingString (n : Nat) : List Nat :=
  decDigits n ++ decDigits (2 * n) ++ decDigits (3 * n)

def digitSet (m : Nat) : Finset Nat := (decDigits m).toFinset

/-- Whenever the function returns a result r, let S(n) be the decimal string obtained by writing n, then 2*n, then 3*n in base 10 without leading zeros. Then r = true if and only if len(S(n)) = 9, S(n) contains no digit '0', and for every d in {1,2,...,9}, the digit d occurs exactly once in S(n); otherwise r = false.
  Preconditions: n is a value of type Std.I64 with 100 <= n <= 999. -/
theorem spec_1 (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999) :
    ∀ r, is_fascinating n = ok r →
      (r = true ↔
        (fascinatingString n.val.toNat).length = 9 ∧
        (∀ d, d ∈ fascinatingString n.val.toNat → d ≠ 0) ∧
        (∀ d, 1 ≤ d → d ≤ 9 → (fascinatingString n.val.toNat).count d = 1)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999), ∀ r, is_fascinating n = ok r →
      (r = true ↔
        (fascinatingString n.val.toNat).length = 9 ∧
        (∀ d, d ∈ fascinatingString n.val.toNat → d ≠ 0) ∧
        (∀ d, 1 ≤ d → d ≤ 9 → (fascinatingString n.val.toNat).count d = 1))) := by
  sorry

/-- For every n with 100 <= n <= 999, the function returns some result r of type Bool; it does not fail, panic, or overflow.
  Preconditions: n is a value of type Std.I64 with 100 <= n <= 999. -/
theorem spec_2 (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999) :
    ∃ r : Bool, is_fascinating n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999), ∃ r : Bool, is_fascinating n = ok r) := by
  sorry

/-- Whenever the function returns a result r, r = false.
  Preconditions: n is a value of type Std.I64 with 334 <= n <= 999. -/
theorem spec_3 (n : Std.I64) (hlo : 334 ≤ n.val) (hhi : n.val ≤ 999) :
    ∀ r, is_fascinating n = ok r → r = false := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (hlo : 334 ≤ n.val) (hhi : n.val ≤ 999), ∀ r, is_fascinating n = ok r → r = false) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the set of decimal digits appearing in n, the set appearing in 2*n, and the set appearing in 3*n are pairwise disjoint.
  Preconditions: n is a value of type Std.I64 with 100 <= n <= 999. -/
theorem spec_4 (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999) :
    ∀ r, is_fascinating n = ok r → r = true →
      (Disjoint (digitSet n.val.toNat) (digitSet (2 * n.val.toNat)) ∧
       Disjoint (digitSet n.val.toNat) (digitSet (3 * n.val.toNat)) ∧
       Disjoint (digitSet (2 * n.val.toNat)) (digitSet (3 * n.val.toNat))) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999), ∀ r, is_fascinating n = ok r → r = true →
      (Disjoint (digitSet n.val.toNat) (digitSet (2 * n.val.toNat)) ∧
       Disjoint (digitSet n.val.toNat) (digitSet (3 * n.val.toNat)) ∧
       Disjoint (digitSet (2 * n.val.toNat)) (digitSet (3 * n.val.toNat)))) := by
  sorry

/-- Whenever the function returns a result r, r = true.
  Preconditions: n = 192. -/
theorem spec_5 (n : Std.I64) (hn : n.val = 192) :
    ∀ r, is_fascinating n = ok r → r = true := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (hn : n.val = 192), ∀ r, is_fascinating n = ok r → r = true) := by
  sorry

/-- Whenever the function returns a result r, if r = true then the sum of all decimal digits in S(n) is 45.
  Preconditions: n is a value of type Std.I64 with 100 <= n <= 999. -/
theorem spec_6 (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999) :
    ∀ r, is_fascinating n = ok r → r = true →
      (fascinatingString n.val.toNat).sum = 45 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999), ∀ r, is_fascinating n = ok r → r = true →
      (fascinatingString n.val.toNat).sum = 45) := by
  sorry

/-- Whenever the function returns a result r, if r = true then n is one of 192, 219, 273, or 327.
  Preconditions: n is a value of type Std.I64 with 100 <= n <= 999. -/
theorem spec_7 (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999) :
    ∀ r, is_fascinating n = ok r → r = true →
      (n.val = 192 ∨ n.val = 219 ∨ n.val = 273 ∨ n.val = 327) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (hlo : 100 ≤ n.val) (hhi : n.val ≤ 999), ∀ r, is_fascinating n = ok r → r = true →
      (n.val = 192 ∨ n.val = 219 ∨ n.val = 273 ∨ n.val = 327)) := by
  sorry

end AegisSpec.IsFascinating
