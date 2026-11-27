import Aegis.NthMagicalNumber.Code.Funs

/-!
# Specifications of `Aegis.NthMagicalNumber.nth_magical_number`

LeetCode problem `nth-magical-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.NthMagicalNumber

def MOD : ℤ := 1000000007

def countC (a b : ℤ) (x : ℤ) : ℕ :=
  ((List.range x.toNat).filter (fun k => decide (a ∣ (k : ℤ) + 1 ∨ b ∣ (k : ℤ) + 1))).length

def IsNthMagical (a b n M : ℤ) : Prop :=
  0 < M ∧ (countC a b (M - 1) : ℤ) < n ∧ n ≤ (countC a b M : ℤ)

def lcmZ (a b : ℤ) : ℤ := (Int.lcm a b : ℤ)

def blockShift (a b : ℤ) : ℤ := lcmZ a b / a + lcmZ a b / b - 1

/-- Let MOD = 1000000007. For an integer x >= 0, let C(x) be the number of positive integers k with 1 <= k <= x and (a divides k or b divides k). Let M be the unique positive integer such that C(M-1) < n <= C(M). Whenever the function returns a result r, r is the unique integer satisfying 0 <= r < MOD and r is congruent to M modulo MOD.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_1 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ M [ZMOD MOD] := by
  sorry

theorem spec_1_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), 0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ M [ZMOD MOD]) := by
  sorry

/-- The function returns a result r; it does not panic, overflow, or otherwise fail for any inputs satisfying the preconditions.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_2 {n a b : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000) :
    ∃ r, Aegis.NthMagicalNumber.nth_magical_number n a b = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ {n a b : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000), ∃ r, Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) := by
  sorry

/-- Let C(x) count the positive integers k with 1 <= k <= x and (a divides k or b divides k), and let M be the unique positive integer such that C(M-1) < n <= C(M). Whenever the function returns r, we have M >= n and r is congruent to M modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_3 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    n.val ≤ M ∧ r.val ≡ M [ZMOD MOD] := by
  sorry

theorem spec_3_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), n.val ≤ M ∧ r.val ≡ M [ZMOD MOD]) := by
  sorry

/-- Let C(x) count the positive integers k with 1 <= k <= x and (a divides k or b divides k), and let M be the unique positive integer such that C(M-1) < n <= C(M). Whenever the function returns r, we have M <= n * min(a,b) and r is congruent to M modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_4 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    M ≤ n.val * min a.val b.val ∧ r.val ≡ M [ZMOD MOD] := by
  sorry

theorem spec_4_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), M ≤ n.val * min a.val b.val ∧ r.val ≡ M [ZMOD MOD]) := by
  sorry

/-- If n = 1, then whenever the function returns r, r = min(a,b).
  Preconditions: n = 1, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_5 {n a b r : Std.I64}
    (hn : n.val = 1)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    r.val = min a.val b.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : n.val = 1)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), r.val = min a.val b.val) := by
  sorry

/-- If a = b, then whenever the function returns r, r is the unique integer satisfying 0 <= r < 1000000007 and r is congruent to n * a modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, 2 <= b <= 40000, and a = b. -/
theorem spec_6 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hab : a.val = b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * a.val [ZMOD MOD] := by
  sorry

theorem spec_6_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hab : a.val = b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), 0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * a.val [ZMOD MOD]) := by
  sorry

/-- If a < b and a divides b, then whenever the function returns r, r is the unique integer satisfying 0 <= r < 1000000007 and r is congruent to n * a modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= a < b <= 40000, and a divides b. -/
theorem spec_7 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (hab : a.val < b.val) (hb' : b.val ≤ 40000)
    (hdvd : a.val ∣ b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * a.val [ZMOD MOD] := by
  sorry

theorem spec_7_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (hab : a.val < b.val) (hb' : b.val ≤ 40000)
    (hdvd : a.val ∣ b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), 0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * a.val [ZMOD MOD]) := by
  sorry

/-- If b < a and b divides a, then whenever the function returns r, r is the unique integer satisfying 0 <= r < 1000000007 and r is congruent to n * b modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= b < a <= 40000, and b divides a. -/
theorem spec_8 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (hb : 2 ≤ b.val) (hba : b.val < a.val) (ha' : a.val ≤ 40000)
    (hdvd : b.val ∣ a.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * b.val [ZMOD MOD] := by
  sorry

theorem spec_8_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (hb : 2 ≤ b.val) (hba : b.val < a.val) (ha' : a.val ≤ 40000)
    (hdvd : b.val ∣ a.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), 0 ≤ r.val ∧ r.val < MOD ∧ r.val ≡ n.val * b.val [ZMOD MOD]) := by
  sorry

/-- If the function returns r for inputs (n,a,b) and returns r' for inputs (n,b,a), then r = r'.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_9 {n a b r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n b a = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ {n a b r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n b a = ok r'), r.val = r'.val) := by
  sorry

/-- Let L = lcm(a,b) and q = L/a + L/b - 1. If the function returns r for n and returns r' for n + q with the same a and b, then r' is congruent to r + L modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, 2 <= b <= 40000, and n + q <= 1000000000, where L = lcm(a,b) and q = L/a + L/b - 1. -/
theorem spec_10 {n a b n' r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hq : n.val + blockShift a.val b.val ≤ 1000000000)
    (hnn' : n'.val = n.val + blockShift a.val b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n' a b = ok r') :
    r' ≡ r + lcmZ a.val b.val [ZMOD MOD] := by
  sorry

theorem spec_10_neg :
    ¬ (∀ {n a b n' r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hq : n.val + blockShift a.val b.val ≤ 1000000000)
    (hnn' : n'.val = n.val + blockShift a.val b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n' a b = ok r'), r' ≡ r + lcmZ a.val b.val [ZMOD MOD]) := by
  sorry

/-- If the function returns r for inputs (n,a,b) and returns r' for inputs (n,c*a,c*b), then r' is congruent to c * r modulo 1000000007.
  Preconditions: 1 <= n <= 1000000000, c >= 1, 2 <= a <= 40000, 2 <= b <= 40000, 2 <= c*a <= 40000, and 2 <= c*b <= 40000. -/
theorem spec_11 {n a b c a' b' r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (hc : 1 ≤ c.val)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hca : 2 ≤ c.val * a.val) (hca' : c.val * a.val ≤ 40000)
    (hcb : 2 ≤ c.val * b.val) (hcb' : c.val * b.val ≤ 40000)
    (ha'a : a'.val = c.val * a.val) (hb'b : b'.val = c.val * b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n a' b' = ok r') :
    r' ≡ c.val * r.val [ZMOD MOD] := by
  sorry

theorem spec_11_neg :
    ¬ (∀ {n a b c a' b' r r' : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (hc : 1 ≤ c.val)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hca : 2 ≤ c.val * a.val) (hca' : c.val * a.val ≤ 40000)
    (hcb : 2 ≤ c.val * b.val) (hcb' : c.val * b.val ≤ 40000)
    (ha'a : a'.val = c.val * a.val) (hb'b : b'.val = c.val * b.val)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r)
    (hr' : Aegis.NthMagicalNumber.nth_magical_number n a' b' = ok r'), r' ≡ c.val * r.val [ZMOD MOD]) := by
  sorry

/-- Let C(x) count the positive integers k with 1 <= k <= x and (a divides k or b divides k), and let M be the unique positive integer such that C(M-1) < n <= C(M). Whenever the function returns r, we have r = M.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, 2 <= b <= 40000, and n * min(a,b) < 1000000007. -/
theorem spec_12 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hsmall : n.val * min a.val b.val < MOD)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    r.val = M := by
  sorry

theorem spec_12_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    (hsmall : n.val * min a.val b.val < MOD)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), r.val = M) := by
  sorry

/-- Let C(x) count the positive integers k with 1 <= k <= x and (a divides k or b divides k), and let M be the unique positive integer such that C(M-1) < n <= C(M). Whenever the function returns r, r is congruent to M modulo 1000000007, M is divisible by a or by b, and C(M) = n.
  Preconditions: 1 <= n <= 1000000000, 2 <= a <= 40000, and 2 <= b <= 40000. -/
theorem spec_13 {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r) :
    r.val ≡ M [ZMOD MOD] ∧ (a.val ∣ M ∨ b.val ∣ M) ∧ (countC a.val b.val M : ℤ) = n.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ {n a b r : Std.I64}
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 1000000000)
    (ha : 2 ≤ a.val) (ha' : a.val ≤ 40000)
    (hb : 2 ≤ b.val) (hb' : b.val ≤ 40000)
    {M : ℤ} (hM : IsNthMagical a.val b.val n.val M)
    (hr : Aegis.NthMagicalNumber.nth_magical_number n a b = ok r), r.val ≡ M [ZMOD MOD] ∧ (a.val ∣ M ∨ b.val ∣ M) ∧ (countC a.val b.val M : ℤ) = n.val) := by
  sorry

end AegisSpec.NthMagicalNumber
