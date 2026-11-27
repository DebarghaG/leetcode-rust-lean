import Aegis.NumSquares.Code.Funs

/-!
# Specifications of `Aegis.NumSquares.num_squares`

LeetCode problem `perfect-squares`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NumSquares

  def IsSumOfSq (n k : ℤ) : Prop :=
    ∃ l : List ℤ, (l.length : ℤ) = k ∧ (∀ a ∈ l, 1 ≤ a) ∧ n = (l.map (fun a => a ^ 2)).sum

  def IsPosSquare (n : ℤ) : Prop :=
    ∃ a : ℤ, 1 ≤ a ∧ n = a ^ 2

  def IsSumTwoPosSquares (n : ℤ) : Prop :=
    ∃ a b : ℤ, 1 ≤ a ∧ 1 ≤ b ∧ n = a ^ 2 + b ^ 2

  def IsSumTwoNonnegSquares (n : ℤ) : Prop :=
    ∃ a b : ℤ, 0 ≤ a ∧ 0 ≤ b ∧ n = a ^ 2 + b ^ 2

  def IsFourPowMulEightVPlusSeven (n : ℤ) : Prop :=
    ∃ u v : ℕ, n = 4 ^ u * (8 * (v : ℤ) + 7)

  /-- Whenever the function returns a result r, the integer value of r is the least m >= 1 such that n can be written as a sum of m positive perfect squares; equivalently, there exist positive integers a_1,...,a_r with n = a_1^2 + ... + a_r^2, and for every integer k with 1 <= k < r there do not exist positive integers b_1,...,b_k with n = b_1^2 + ... + b_k^2.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000 (the LeetCode constraint n <= 10^4). -/
  theorem spec_1 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      IsSumOfSq n.val r.val ∧ ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ IsSumOfSq n.val k := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), IsSumOfSq n.val r.val ∧ ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ IsSumOfSq n.val k) := by
    sorry

  /-- For every such n, there exists an integer r such that the function returns Result.ok r; in other words, the function does not fail on any input in the problem constraints.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_2 (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000) :
      ∃ r : Std.I64, Aegis.NumSquares.num_squares n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000), ∃ r : Std.I64, Aegis.NumSquares.num_squares n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is at least 1.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_3 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      1 ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), 1 ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, the integer value of r is at most 4.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_4 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val ≤ 4 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val ≤ 4) := by
    sorry

  /-- Whenever the function returns a result r, r = 1 if and only if there exists an integer a >= 1 such that n = a*a.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_5 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val = 1 ↔ IsPosSquare n.val := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val = 1 ↔ IsPosSquare n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 2 if and only if both of the following hold: (i) there exist integers a >= 1 and b >= 1 such that n = a*a + b*b; (ii) there is no integer c >= 1 such that n = c*c.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_6 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val = 2 ↔ IsSumTwoPosSquares n.val ∧ ¬ IsPosSquare n.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val = 2 ↔ IsSumTwoPosSquares n.val ∧ ¬ IsPosSquare n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 3 if and only if all of the following hold: (a) there is no integer a >= 1 with n = a*a; (b) there are no integers a >= 1 and b >= 1 with n = a*a + b*b; (c) there do not exist integers u >= 0 and v >= 0 with n = 4^u * (8*v + 7).
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_7 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val = 3 ↔ ¬ IsPosSquare n.val ∧ ¬ IsSumTwoPosSquares n.val ∧
        ¬ IsFourPowMulEightVPlusSeven n.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val = 3 ↔ ¬ IsPosSquare n.val ∧ ¬ IsSumTwoPosSquares n.val ∧
          ¬ IsFourPowMulEightVPlusSeven n.val) := by
    sorry

  /-- Whenever the function returns a result r, r = 4 if and only if there exist integers u >= 0 and v >= 0 such that n = 4^u * (8*v + 7).
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_8 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val = 4 ↔ IsFourPowMulEightVPlusSeven n.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val = 4 ↔ IsFourPowMulEightVPlusSeven n.val) := by
    sorry

  /-- Whenever the function returns a result r, there exist positive integers a_1,...,a_r such that n = a_1^2 + ... + a_r^2.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_9 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      IsSumOfSq n.val r.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), IsSumOfSq n.val r.val) := by
    sorry

  /-- Whenever the function returns a result r, for every integer k with 1 <= k < r there do not exist positive integers b_1,...,b_k such that n = b_1^2 + ... + b_k^2.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_10 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ IsSumOfSq n.val k := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), ∀ k : ℤ, 1 ≤ k → k < r.val → ¬ IsSumOfSq n.val k) := by
    sorry

  /-- Whenever the function returns r on input n and s on input k*k*n, we have r = s.
    Preconditions: The integers n and k satisfy 1 <= n, 1 <= k, and k*k*n <= 10000. -/
  theorem spec_11 (n k m r s : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val)
      (hnk : k.val * k.val * n.val ≤ 10000) (hm : m.val = k.val * k.val * n.val)
      (hr : Aegis.NumSquares.num_squares n = ok r)
      (hs : Aegis.NumSquares.num_squares m = ok s) :
      r.val = s.val := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n k m r s : Std.I64) (hn : 1 ≤ n.val) (hk : 1 ≤ k.val)
        (hnk : k.val * k.val * n.val ≤ 10000) (hm : m.val = k.val * k.val * n.val)
        (hr : Aegis.NumSquares.num_squares n = ok r)
        (hs : Aegis.NumSquares.num_squares m = ok s), r.val = s.val) := by
    sorry

  /-- Whenever the function returns ra on input a, rb on input b, and rs on input a+b, we have rs <= ra + rb.
    Preconditions: The integers a and b satisfy 1 <= a, 1 <= b, and a + b <= 10000. -/
  theorem spec_12 (a b s ra rb rs : Std.I64) (ha : 1 ≤ a.val) (hb : 1 ≤ b.val)
      (hab : a.val + b.val ≤ 10000) (hs : s.val = a.val + b.val)
      (hra : Aegis.NumSquares.num_squares a = ok ra)
      (hrb : Aegis.NumSquares.num_squares b = ok rb)
      (hrs : Aegis.NumSquares.num_squares s = ok rs) :
      rs.val ≤ ra.val + rb.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (a b s ra rb rs : Std.I64) (ha : 1 ≤ a.val) (hb : 1 ≤ b.val)
        (hab : a.val + b.val ≤ 10000) (hs : s.val = a.val + b.val)
        (hra : Aegis.NumSquares.num_squares a = ok ra)
        (hrb : Aegis.NumSquares.num_squares b = ok rb)
        (hrs : Aegis.NumSquares.num_squares s = ok rs), rs.val ≤ ra.val + rb.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2 if and only if there exist integers a >= 0 and b >= 0 such that n = a*a + b*b.
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_13 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val ≤ 2 ↔ IsSumTwoNonnegSquares n.val := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val ≤ 2 ↔ IsSumTwoNonnegSquares n.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 3 if and only if there do not exist integers u >= 0 and v >= 0 such that n = 4^u * (8*v + 7).
    Preconditions: The integer value of the input n satisfies 1 <= n <= 10000. -/
  theorem spec_14 (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
      (hr : Aegis.NumSquares.num_squares n = ok r) :
      r.val ≤ 3 ↔ ¬ IsFourPowMulEightVPlusSeven n.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (n r : Std.I64) (hn : 1 ≤ n.val ∧ n.val ≤ 10000)
        (hr : Aegis.NumSquares.num_squares n = ok r), r.val ≤ 3 ↔ ¬ IsFourPowMulEightVPlusSeven n.val) := by
    sorry

  end AegisSpec.NumSquares
