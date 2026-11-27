import Aegis.ClimbStairs.Code.Funs

/-!
# Specifications of `Aegis.ClimbStairs.climb_stairs`

LeetCode problem `climbing-stairs`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.ClimbStairs

  def IsCompOf (n : Nat) (l : List Nat) : Prop :=
    l ≠ [] ∧ (∀ s ∈ l, s = 1 ∨ s = 2) ∧ l.sum = n

  noncomputable def W (n : Nat) : Nat := Nat.card { l : List Nat // IsCompOf n l }

  def Fib : Nat → Nat
    | 0 => 0
    | 1 => 1
    | k + 2 => Fib (k + 1) + Fib k

  def binomSum (n : Nat) : Nat :=
    ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose (n - j) j

  /-- Let W(n) be the number of finite ordered sequences (s_1,...,s_k) with k >= 1, each s_j equal to 1 or 2, and sum_{j=1}^k s_j = n. The function returns a result r and r = W(n).
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_1 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45) :
      ∃ r : Std.I64, Aegis.ClimbStairs.climb_stairs n = ok r ∧ r.val = (W n.val.toNat : Int) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45), ∃ r : Std.I64, Aegis.ClimbStairs.climb_stairs n = ok r ∧ r.val = (W n.val.toNat : Int)) := by
    sorry

  /-- The function returns a result r; it does not panic, overflow, go out of bounds, or otherwise fail.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_2 (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45) :
      ∃ r : Std.I64, Aegis.ClimbStairs.climb_stairs n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45), ∃ r : Std.I64, Aegis.ClimbStairs.climb_stairs n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 1836311903.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_3 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      1 ≤ r.val ∧ r.val ≤ 1836311903 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), 1 ≤ r.val ∧ r.val ≤ 1836311903) := by
    sorry

  /-- Whenever the function returns a result r, r >= n.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_4 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      n.val ≤ r.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), n.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2^(n-1), where 2^(n-1) is the integer power.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_5 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      r.val ≤ 2 ^ (n.val.toNat - 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), r.val ≤ 2 ^ (n.val.toNat - 1)) := by
    sorry

  /-- Whenever the function returns results r, r1, and r2 for inputs n, n-1, and n-2 respectively, it holds that r = r1 + r2.
    Preconditions: 3 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_6 (n n1 n2 r r1 r2 : Std.I64) (hlo : 3 ≤ n.val) (hhi : n.val ≤ 45)
      (hn1 : n1.val = n.val - 1) (hn2 : n2.val = n.val - 2)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r)
      (hr1 : Aegis.ClimbStairs.climb_stairs n1 = ok r1)
      (hr2 : Aegis.ClimbStairs.climb_stairs n2 = ok r2) :
      r.val = r1.val + r2.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n n1 n2 r r1 r2 : Std.I64) (hlo : 3 ≤ n.val) (hhi : n.val ≤ 45)
        (hn1 : n1.val = n.val - 1) (hn2 : n2.val = n.val - 2)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r)
        (hr1 : Aegis.ClimbStairs.climb_stairs n1 = ok r1)
        (hr2 : Aegis.ClimbStairs.climb_stairs n2 = ok r2), r.val = r1.val + r2.val) := by
    sorry

  /-- Whenever the function returns results rn for input n and rm for input m, rn < rm.
    Preconditions: 1 <= n < m <= 45, where n and m are Std.I64 values. -/
  theorem spec_7 (n m rn rm : Std.I64) (hlo : 1 ≤ n.val) (hlt : n.val < m.val)
      (hhi : m.val ≤ 45)
      (hrn : Aegis.ClimbStairs.climb_stairs n = ok rn)
      (hrm : Aegis.ClimbStairs.climb_stairs m = ok rm) :
      rn.val < rm.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m rn rm : Std.I64) (hlo : 1 ≤ n.val) (hlt : n.val < m.val)
        (hhi : m.val ≤ 45)
        (hrn : Aegis.ClimbStairs.climb_stairs n = ok rn)
        (hrm : Aegis.ClimbStairs.climb_stairs m = ok rm), rn.val < rm.val) := by
    sorry

  /-- Let F be defined by F_1 = 1, F_2 = 1, and F_{k+2} = F_{k+1} + F_k for all k >= 1. Whenever the function returns a result r, r = F_{n+1}.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_8 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      r.val = (Fib (n.val.toNat + 1) : Int) := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), r.val = (Fib (n.val.toNat + 1) : Int)) := by
    sorry

  /-- Whenever the function returns a result r, r is even if and only if n is congruent to 2 modulo 3; if n is not congruent to 2 modulo 3, r is odd.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_9 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      (Even r.val ↔ ∃ k : Int, n.val = 3 * k + 2) ∧
        ((¬ ∃ k : Int, n.val = 3 * k + 2) → Odd r.val) := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), (Even r.val ↔ ∃ k : Int, n.val = 3 * k + 2) ∧
          ((¬ ∃ k : Int, n.val = 3 * k + 2) → Odd r.val)) := by
    sorry

  /-- Whenever the function returns a result r, r = sum_{j=0}^{floor(n/2)} C(n-j, j), where C(a,b) is the binomial coefficient counting the number of ways to choose b elements from a.
    Preconditions: 1 <= n <= 45, where n is the Std.I64 parameter. -/
  theorem spec_10 (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
      (hr : Aegis.ClimbStairs.climb_stairs n = ok r) :
      r.val = (binomSum n.val.toNat : Int) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n r : Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 45)
        (hr : Aegis.ClimbStairs.climb_stairs n = ok r), r.val = (binomSum n.val.toNat : Int)) := by
    sorry

  end AegisSpec.ClimbStairs
