import Aegis.ArrangeCoins.Code.Funs

/-!
# Specifications of `Aegis.ArrangeCoins.arrange_coins`

LeetCode problem `arranging-coins`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.ArrangeCoins (arrange_coins)

namespace AegisSpec.ArrangeCoins

def T (k : Int) : Int := k * (k + 1) / 2

def IsTriangular (m : Int) : Prop := ∃ k : Int, 1 ≤ k ∧ m = T k

def succ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) : Std.I64 :=
  Std.I64.ofInt (n.val + 1) (by
    simp [Aeneas.Std.IScalar.cMin, Aeneas.Std.IScalar.cMax, Aeneas.Std.IScalar.rMin,
      Aeneas.Std.IScalar.rMax, Aeneas.Std.I64.rMin, Aeneas.Std.I64.rMax]
    omega)

@[simp]
theorem succ_val (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) :
    (succ n h1 h2).val = n.val + 1 := by
  rw [succ]
  simp only [Aeneas.Std.I64.ofInt, Aeneas.Std.IScalar.ofInt, Aeneas.Std.IScalar.val,
    Aeneas.Std.IScalar.ofIntCore_bv, BitVec.toInt_ofInt, Aeneas.Std.IScalarTy.numBits]
  have hv : n.bv.toInt = (n.val : Int) := Aeneas.Std.IScalar.bv_toInt_eq n
  have h3 : n.bv.toInt + 1 < 2 ^ 63 := by omega
  have h4 : -(2 ^ 63) ≤ n.bv.toInt + 1 := by omega
  exact
    Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 64 (n.bv.toInt + 1) (by norm_num)
      (by simpa using h4) (by simpa using h3)

/-- Let T(k) = k(k+1)/2 for integer k >= 0. The function returns a result r and r is the unique integer such that r >= 0, T(r) <= n, and n < T(r+1). Equivalently, r is the number of complete rows in the staircase built with n coins, where row i contains i coins for each complete row i.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_1 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) :
    ∃ r : Std.I64, arrange_coins n = ok r ∧ 0 ≤ r.val ∧ T r.val ≤ n.val ∧
      n.val < T (r.val + 1) ∧
      ∀ r' : Int, 0 ≤ r' → T r' ≤ n.val → n.val < T (r' + 1) → r' = r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647), ∃ r : Std.I64, arrange_coins n = ok r ∧ 0 ≤ r.val ∧ T r.val ≤ n.val ∧
      n.val < T (r.val + 1) ∧
      ∀ r' : Int, 0 ≤ r' → T r' ≤ n.val → n.val < T (r' + 1) → r' = r.val) := by
  sorry

/-- For every such n, the function returns some result r; it does not fail, panic, or overflow.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_2 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) :
    ∃ r : Std.I64, arrange_coins n = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647), ∃ r : Std.I64, arrange_coins n = ok r) := by
  sorry

/-- Whenever the function returns a result r, we have 1 <= r.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_3 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r), 1 ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, we have r <= n.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_4 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r), r.val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, we have r <= 65535.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_5 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    r.val ≤ 65535 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r), r.val ≤ 65535) := by
  sorry

/-- The function returns the result r = 1.
  Preconditions: n = 1. -/
theorem spec_6 (n : Std.I64) (h : n.val = 1) :
    ∃ r : Std.I64, arrange_coins n = ok r ∧ r.val = 1 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Std.I64) (h : n.val = 1), ∃ r : Std.I64, arrange_coins n = ok r ∧ r.val = 1) := by
  sorry

/-- The function returns the result r = 65535.
  Preconditions: n = 2147483647. -/
theorem spec_7 (n : Std.I64) (h : n.val = 2147483647) :
    ∃ r : Std.I64, arrange_coins n = ok r ∧ r.val = 65535 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Std.I64) (h : n.val = 2147483647), ∃ r : Std.I64, arrange_coins n = ok r ∧ r.val = 65535) := by
  sorry

/-- Let T(k) = k(k+1)/2. For every integer k with 2 <= k <= 65535, if n = T(k), then whenever the function returns a result r, we have r = k.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_8 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    r.val = k := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k) (r : Std.I64)
    (hr : arrange_coins n = ok r), r.val = k) := by
  sorry

/-- Let T(k) = k(k+1)/2. For every integer k with 2 <= k <= 65535, if n = T(k) - 1, then whenever the function returns a result r, we have r = k - 1.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_9 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k - 1) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    r.val = k - 1 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k - 1) (r : Std.I64)
    (hr : arrange_coins n = ok r), r.val = k - 1) := by
  sorry

/-- Let T(k) = k(k+1)/2. For every integer k with 2 <= k <= 65535, if n = T(k) + 1, then whenever the function returns a result r, we have r = k.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_10 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k + 1) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    r.val = k := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (k : Int)
    (hk1 : 2 ≤ k) (hk2 : k ≤ 65535) (hn : n.val = T k + 1) (r : Std.I64)
    (hr : arrange_coins n = ok r), r.val = k) := by
  sorry

/-- Let T(k) = k(k+1)/2. Whenever the function returns a result r, let m = n - T(r). Then 0 <= m <= r; m is exactly the number of coins left after r complete rows, and these m coins form the next incomplete row if m > 0, or no incomplete row exists if m = 0.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_11 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) :
    0 ≤ n.val - T r.val ∧ n.val - T r.val ≤ r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r), 0 ≤ n.val - T r.val ∧ n.val - T r.val ≤ r.val) := by
  sorry

/-- Whenever arrange_coins(n1) returns r1 and arrange_coins(n2) returns r2, we have r1 <= r2.
  Preconditions: n1 and n2 are integers with 1 <= n1 <= n2 <= 2147483647. -/
theorem spec_12 (n1 n2 : Std.I64) (h1 : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val)
    (h2 : n2.val ≤ 2147483647) (r1 r2 : Std.I64) (hr1 : arrange_coins n1 = ok r1)
    (hr2 : arrange_coins n2 = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n1 n2 : Std.I64) (h1 : 1 ≤ n1.val) (h12 : n1.val ≤ n2.val)
    (h2 : n2.val ≤ 2147483647) (r1 r2 : Std.I64) (hr1 : arrange_coins n1 = ok r1)
    (hr2 : arrange_coins n2 = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- Whenever arrange_coins(n) returns r and arrange_coins(n+1) returns s, the difference s - r is either 0 or 1.
  Preconditions: The value of n is an integer with 1 <= n < 2147483647. -/
theorem spec_13 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) (r s : Std.I64)
    (hr : arrange_coins n = ok r) (hs : arrange_coins (succ n h1 h2) = ok s) :
    s.val - r.val = 0 ∨ s.val - r.val = 1 := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) (r s : Std.I64)
    (hr : arrange_coins n = ok r) (hs : arrange_coins (succ n h1 h2) = ok s), s.val - r.val = 0 ∨ s.val - r.val = 1) := by
  sorry

/-- Let T(k) = k(k+1)/2. Whenever arrange_coins(n) returns r and arrange_coins(n+1) returns s, we have s = r + 1 if and only if n + 1 = T(k) for some integer k >= 1; otherwise s = r.
  Preconditions: The value of n is an integer with 1 <= n < 2147483647. -/
theorem spec_14 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) (r s : Std.I64)
    (hr : arrange_coins n = ok r) (hs : arrange_coins (succ n h1 h2) = ok s) :
    (s.val = r.val + 1 ↔ IsTriangular (n.val + 1)) ∧
      (¬ IsTriangular (n.val + 1) → s.val = r.val) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val < 2147483647) (r s : Std.I64)
    (hr : arrange_coins n = ok r) (hs : arrange_coins (succ n h1 h2) = ok s), (s.val = r.val + 1 ↔ IsTriangular (n.val + 1)) ∧
      (¬ IsTriangular (n.val + 1) → s.val = r.val)) := by
  sorry

/-- Let T(k) = k(k+1)/2. Whenever the function returns a result r, for every integer k with r < k <= 65536, we have T(k) > n.
  Preconditions: The value of n is an integer with 1 <= n <= 2147483647. -/
theorem spec_15 (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) (k : Int) (hk1 : r.val < k) (hk2 : k ≤ 65536) :
    T k > n.val := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Std.I64) (h1 : 1 ≤ n.val) (h2 : n.val ≤ 2147483647) (r : Std.I64)
    (hr : arrange_coins n = ok r) (k : Int) (hk1 : r.val < k) (hk2 : k ≤ 65536), T k > n.val) := by
  sorry

end AegisSpec.ArrangeCoins
