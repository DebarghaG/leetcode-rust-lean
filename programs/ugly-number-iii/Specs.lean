import Aegis.NthUglyNumber.Code.Funs

/-!
# Specifications of `Aegis.NthUglyNumber.nth_ugly_number`

LeetCode problem `ugly-number-iii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NthUglyNumber

def IsUgly (a b c x : ℤ) : Prop :=
  0 < x ∧ (x % a = 0 ∨ x % b = 0 ∨ x % c = 0)

def IsUgly2 (a c x : ℤ) : Prop :=
  0 < x ∧ (x % a = 0 ∨ x % c = 0)

def countBelow (P : ℤ → Prop) [DecidablePred P] (r : ℤ) : ℤ :=
  (((Finset.range (r - 1).toNat).filter (fun k : ℕ => P ((k : ℤ) + 1))).card : ℤ)

instance (a b c : ℤ) : DecidablePred (IsUgly a b c) := by
  intro x
  unfold IsUgly
  infer_instance

instance (a c : ℤ) : DecidablePred (IsUgly2 a c) := by
  intro x
  unfold IsUgly2
  infer_instance

def IsNthSmallest (P : ℤ → Prop) [DecidablePred P] (n r : ℤ) : Prop :=
  P r ∧ countBelow P r = n - 1

def IsNthUgly (a b c n r : ℤ) : Prop :=
  IsNthSmallest (IsUgly a b c) n r

def IsNthUgly2 (a c n r : ℤ) : Prop :=
  IsNthSmallest (IsUgly2 a c) n r

def NthUglyLe (a b c n B : ℤ) : Prop :=
  ∃ r : ℤ, IsNthUgly a b c n r ∧ r ≤ B

def IsPerm3 (a b c a' b' c' : ℤ) : Prop :=
  (a' = a ∧ b' = b ∧ c' = c) ∨
  (a' = a ∧ b' = c ∧ c' = b) ∨
  (a' = b ∧ b' = a ∧ c' = c) ∨
  (a' = b ∧ b' = c ∧ c' = a) ∨
  (a' = c ∧ b' = a ∧ c' = b) ∨
  (a' = c ∧ b' = b ∧ c' = a)

/-- Let U be the set of positive integers x such that x mod a = 0 or x mod b = 0 or x mod c = 0. The function returns a result r such that, interpreting r as a natural number, r is the n-th smallest element of U (i.e., r is in U and there are exactly n-1 elements of U that are strictly less than r).
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_1 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000) :
    ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      IsNthUgly a.val b.val c.val n.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      IsNthUgly a.val b.val c.val n.val r.val) := by
  sorry

/-- The function returns r such that r is the n-th smallest positive integer x with (x mod a = 0 or x mod c = 0). In other words, the condition x mod b = 0 is redundant because every multiple of b is already a multiple of a.
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; a divides b (i.e., b mod a = 0); the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_2 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hdiv : b.val % a.val = 0)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000) :
    ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      IsNthUgly2 a.val c.val n.val r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hdiv : b.val % a.val = 0)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      IsNthUgly2 a.val c.val n.val r.val) := by
  sorry

/-- If r1 is the result returned for n1 (with the same a, b, c) and r2 is the result returned for n2, then r1 < r2.
  Preconditions: 1 <= n1 < n2 <= 1000000000; 1 <= a, b, c <= 1000000000; a * b * c <= 1000000000000000000; both the n1-th and n2-th smallest positive integers divisible by at least one of a, b, c are at most 2000000000. -/
theorem spec_3 (n1 n2 a b c : Std.I64)
    (hn1 : 1 ≤ n1.val) (hlt : n1.val < n2.val) (hn2 : n2.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound1 : NthUglyLe a.val b.val c.val n1.val 2000000000)
    (hbound2 : NthUglyLe a.val b.val c.val n2.val 2000000000)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.NthUglyNumber.nth_ugly_number n1 a b c = ok r1)
    (hr2 : Aegis.NthUglyNumber.nth_ugly_number n2 a b c = ok r2) :
    r1.val < r2.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n1 n2 a b c : Std.I64)
    (hn1 : 1 ≤ n1.val) (hlt : n1.val < n2.val) (hn2 : n2.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound1 : NthUglyLe a.val b.val c.val n1.val 2000000000)
    (hbound2 : NthUglyLe a.val b.val c.val n2.val 2000000000)
    (r1 r2 : Std.I64)
    (hr1 : Aegis.NthUglyNumber.nth_ugly_number n1 a b c = ok r1)
    (hr2 : Aegis.NthUglyNumber.nth_ugly_number n2 a b c = ok r2), r1.val < r2.val) := by
  sorry

/-- If r is the result for (n, a, b, c) and r' is the result for (n, k*a, k*b, k*c), then r' = k * r.
  Preconditions: 1 <= n <= 1000000000; 1 <= a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000; k is a positive integer such that k*a, k*b, k*c <= 1000000000 and (k*a)*(k*b)*(k*c) <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of k*a, k*b, k*c is at most 2000000000. -/
theorem spec_4 (n a b c k a' b' c' : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (hk : 1 ≤ k.val)
    (hka : a'.val = k.val * a.val) (hkb : b'.val = k.val * b.val)
    (hkc : c'.val = k.val * c.val)
    (hka' : a'.val ≤ 1000000000) (hkb' : b'.val ≤ 1000000000) (hkc' : c'.val ≤ 1000000000)
    (habc' : a'.val * b'.val * c'.val ≤ 1000000000000000000)
    (hbound' : NthUglyLe a'.val b'.val c'.val n.val 2000000000)
    (r r' : Std.I64)
    (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r)
    (hr' : Aegis.NthUglyNumber.nth_ugly_number n a' b' c' = ok r') :
    r'.val = k.val * r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n a b c k a' b' c' : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (hk : 1 ≤ k.val)
    (hka : a'.val = k.val * a.val) (hkb : b'.val = k.val * b.val)
    (hkc : c'.val = k.val * c.val)
    (hka' : a'.val ≤ 1000000000) (hkb' : b'.val ≤ 1000000000) (hkc' : c'.val ≤ 1000000000)
    (habc' : a'.val * b'.val * c'.val ≤ 1000000000000000000)
    (hbound' : NthUglyLe a'.val b'.val c'.val n.val 2000000000)
    (r r' : Std.I64)
    (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r)
    (hr' : Aegis.NthUglyNumber.nth_ugly_number n a' b' c' = ok r'), r'.val = k.val * r.val) := by
  sorry

/-- The returned value r satisfies r >= n.
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_5 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r) :
    n.val ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r), n.val ≤ r.val) := by
  sorry

/-- The returned value r satisfies r >= min(a, b, c).
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_6 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r) :
    min a.val (min b.val c.val) ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r), min a.val (min b.val c.val) ≤ r.val) := by
  sorry

/-- The returned value r satisfies r <= n * min(a, b, c).
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_7 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r) :
    r.val ≤ n.val * min a.val (min b.val c.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r), r.val ≤ n.val * min a.val (min b.val c.val)) := by
  sorry

/-- The function returns a result (it does not fail) for every input satisfying the preconditions.
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_8 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000) :
    ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r) := by
  sorry

/-- For any permutation (a', b', c') of (a, b, c), the returned value r is also the n-th smallest positive integer divisible by at least one of a', b', c'.
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_9 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r) :
    ∀ a' b' c' : Std.I64,
      IsPerm3 a.val b.val c.val a'.val b'.val c'.val →
      IsNthUgly a'.val b'.val c'.val n.val r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000)
    (r : Std.I64) (hr : Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r), ∀ a' b' c' : Std.I64,
      IsPerm3 a.val b.val c.val a'.val b'.val c'.val →
      IsNthUgly a'.val b'.val c'.val n.val r.val) := by
  sorry

/-- The function returns r = n * a.
  Preconditions: 1 <= n, a, b, c <= 1000000000; a * b * c <= 1000000000000000000; a divides b and b divides c; the n-th smallest positive integer divisible by at least one of a, b, c is at most 2000000000. -/
theorem spec_10 (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hdivab : b.val % a.val = 0)
    (hdivbc : c.val % b.val = 0)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000) :
    ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      r.val = n.val * a.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n a b c : Std.I64)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 1 ≤ a.val) (ha' : a.val ≤ 1000000000)
    (hb : 1 ≤ b.val) (hb' : b.val ≤ 1000000000)
    (hc : 1 ≤ c.val) (hc' : c.val ≤ 1000000000)
    (habc : a.val * b.val * c.val ≤ 1000000000000000000)
    (hdivab : b.val % a.val = 0)
    (hdivbc : c.val % b.val = 0)
    (hbound : NthUglyLe a.val b.val c.val n.val 2000000000), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n a b c = ok r ∧
      r.val = n.val * a.val) := by
  sorry

end AegisSpec.NthUglyNumber
