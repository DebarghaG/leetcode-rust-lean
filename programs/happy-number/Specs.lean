import Aegis.IsHappy.Code.Funs

/-!
# Specifications of `Aegis.IsHappy.is_happy`

LeetCode problem `happy-number`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.IsHappy

def decimalDigits (m : Nat) : List Nat :=
  if h : m = 0 then [] else m % 10 :: decimalDigits (m / 10)
termination_by m
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def digitSquareSum (m : Nat) : Nat := ((decimalDigits m).map fun d => d ^ 2).sum

def D (m : ℤ) : ℤ := (digitSquareSum m.natAbs : ℤ)

def happyCycle : List ℤ := [4, 16, 37, 58, 89, 145, 42, 20]

def InHappyCycle (m : ℤ) : Prop := m ∈ happyCycle

def SameDigits (N M : ℤ) : Prop :=
  (decimalDigits N.natAbs).length = (decimalDigits M.natAbs).length ∧
    (decimalDigits N.natAbs).Perm (decimalDigits M.natAbs)

/-- Whenever is_happy(n) returns a result r, r = true if and only if there exists k >= 0 such that D^k(N) = 1.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Define D(m) for positive integers m as the sum of the squares of the decimal digits of m, and define D^0(m)=m and D^{k+1}(m)=D(D^k(m)) for k >= 0. -/
theorem spec_1 (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) :
    (r = true ↔ ∃ k : Nat, (D^[k]) N = 1) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r), (r = true ↔ ∃ k : Nat, (D^[k]) N = 1)) := by
  sorry

/-- is_happy(n) returns a result r; it does not fail, panic, or overflow for any n in the stated range.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. -/
theorem spec_2 (n : Std.I64) (N : ℤ)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647) :
    ∃ r : Bool, Aegis.IsHappy.is_happy n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647), ∃ r : Bool, Aegis.IsHappy.is_happy n = ok r) := by
  sorry

/-- Whenever is_happy(n) returns a result r, r = false if and only if there exists k >= 0 such that D^k(N) = 4.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Define D(m) as the sum of the squares of the decimal digits of m, and D^0(m)=m, D^{k+1}(m)=D(D^k(m)). -/
theorem spec_3 (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) :
    (r = false ↔ ∃ k : Nat, (D^[k]) N = 4) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r), (r = false ↔ ∃ k : Nat, (D^[k]) N = 4)) := by
  sorry

/-- Whenever is_happy(n) returns a result r, r = true if and only if D^10000(N) = 1.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Define D(m) as the sum of the squares of the decimal digits of m, and D^0(m)=m, D^{k+1}(m)=D(D^k(m)). -/
theorem spec_4 (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) :
    (r = true ↔ (D^[10000]) N = 1) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r), (r = true ↔ (D^[10000]) N = 1)) := by
  sorry

/-- Whenever is_happy(n) returns r and is_happy(m) returns s, r = s.
  Preconditions: Let N and M be the integer values of two I64 inputs n and m, with 1 <= N <= 2147483647 and 1 <= M <= 2147483647. The decimal representations of N and M have the same length and the same multiset of decimal digits (equivalently, M is obtained by permuting the digits of N without dropping or introducing a leading zero). Define D(m) as the sum of the squares of the decimal digits of m. -/
theorem spec_5 (n m : Std.I64) (N M : ℤ) (r s : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hM : m.val = M) (hM_low : 1 ≤ M) (hM_high : M ≤ 2147483647)
    (hd : SameDigits N M)
    (hr : Aegis.IsHappy.is_happy n = ok r)
    (hs : Aegis.IsHappy.is_happy m = ok s) :
    r = s := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n m : Std.I64) (N M : ℤ) (r s : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hM : m.val = M) (hM_low : 1 ≤ M) (hM_high : M ≤ 2147483647)
    (hd : SameDigits N M)
    (hr : Aegis.IsHappy.is_happy n = ok r)
    (hs : Aegis.IsHappy.is_happy m = ok s), r = s) := by
  sorry

/-- Whenever is_happy(n) returns r and is_happy(the I64 whose integer value is D^k(N)) returns s, r = s.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Let k >= 0 be an integer. Define D(m) as the sum of the squares of the decimal digits of m, and D^0(m)=m, D^{k+1}(m)=D(D^k(m)). -/
theorem spec_6 (n m : Std.I64) (N : ℤ) (k : Nat) (r s : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hm : m.val = (D^[k]) N)
    (hr : Aegis.IsHappy.is_happy n = ok r)
    (hs : Aegis.IsHappy.is_happy m = ok s) :
    r = s := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n m : Std.I64) (N : ℤ) (k : Nat) (r s : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hm : m.val = (D^[k]) N)
    (hr : Aegis.IsHappy.is_happy n = ok r)
    (hs : Aegis.IsHappy.is_happy m = ok s), r = s) := by
  sorry

/-- Whenever is_happy(n) returns a result r, r = false if and only if there exists k >= 0 such that D^k(N) is in C. Moreover, for every positive integer M whose D-orbit does not reach 1, the orbit eventually enters C and then cycles in the order 4 -> 16 -> 37 -> 58 -> 89 -> 145 -> 42 -> 20 -> 4; no other non-happy cycle occurs.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Define D(m) as the sum of the squares of the decimal digits of m, and D^0(m)=m, D^{k+1}(m)=D(D^k(m)). Let C = {4,16,37,58,89,145,42,20}. -/
theorem spec_7 (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) :
    (r = false ↔ ∃ k : Nat, InHappyCycle ((D^[k]) N)) ∧
      (∀ M : ℤ, 1 ≤ M → (¬ ∃ k : Nat, (D^[k]) M = 1) →
        ∃ j : Nat, (D^[j]) M = 4 ∧ ∀ t : Nat, (D^[j + t]) M = (D^[t]) 4) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r), (r = false ↔ ∃ k : Nat, InHappyCycle ((D^[k]) N)) ∧
      (∀ M : ℤ, 1 ≤ M → (¬ ∃ k : Nat, (D^[k]) M = 1) →
        ∃ j : Nat, (D^[j]) M = 4 ∧ ∀ t : Nat, (D^[j + t]) M = (D^[t]) 4)) := by
  sorry

/-- Whenever is_happy(n) returns a result r and r = false, D^10000(N) is an element of C.
  Preconditions: n is an I64 whose integer value N satisfies 1 <= N <= 2147483647. Define D(m) as the sum of the squares of the decimal digits of m, and D^0(m)=m, D^{k+1}(m)=D(D^k(m)). Let C = {4,16,37,58,89,145,42,20}. -/
theorem spec_8 (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) (hrfalse : r = false) :
    InHappyCycle ((D^[10000]) N) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (N : ℤ) (r : Bool)
    (hN : n.val = N) (hN_low : 1 ≤ N) (hN_high : N ≤ 2147483647)
    (hr : Aegis.IsHappy.is_happy n = ok r) (hrfalse : r = false), InHappyCycle ((D^[10000]) N)) := by
  sorry

end AegisSpec.IsHappy
