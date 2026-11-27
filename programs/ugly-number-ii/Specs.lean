import Aegis.NthUglyNumber.Code.Funs

/-!
# Specifications of `Aegis.NthUglyNumber.nth_ugly_number`

LeetCode problem `ugly-number-ii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.NthUglyNumber

  def Ugly (k : Int) : Prop :=
    0 < k ∧ ∀ p : Nat, p.Prime → (p : Int) ∣ k → p = 2 ∨ p = 3 ∨ p = 5

  noncomputable def uglyCountBelow (r : Int) : Nat := by
    classical
    exact ((Finset.Icc 1 (Int.toNat (r - 1))).filter (fun k : Nat => Ugly (k : Int))).card

  /-- Let Ugly(k) mean that k is a positive integer and every prime divisor of k is one of 2, 3, and 5; equivalently, k = 2^a * 3^b * 5^c for some nonnegative integers a, b, c (so Ugly(1) holds). The function returns a result r, and r is the n-th element (1-indexed) of the increasing sequence of all ugly numbers: Ugly(r) holds and exactly n - 1 positive integers k < r satisfy Ugly(k).
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_1 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690) :
      ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧
        Ugly r.val ∧ (uglyCountBelow r.val : Int) = n.val - 1 := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧
          Ugly r.val ∧ (uglyCountBelow r.val : Int) = n.val - 1) := by
    sorry

  /-- The function returns a result r; it does not fail, panic, or report arithmetic overflow.
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_2 (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690) :
      ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= n.
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_3 (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r) :
      n.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r), n.val ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, r <= 2123366400.
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_4 (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r) :
      r.val ≤ 2123366400 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r), r.val ≤ 2123366400) := by
    sorry

  /-- The function returns a result r and r = 1.
    Preconditions: n = 1. -/
  theorem spec_5 (n : Std.I64) (hn : n.val = 1) :
      ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = 1) := by
    sorry

  /-- The function returns a result r and r = 2123366400.
    Preconditions: n = 1690. -/
  theorem spec_6 (n : Std.I64) (hn : n.val = 1690) :
      ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = 2123366400 := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Std.I64) (hn : n.val = 1690), ∃ r : Std.I64, Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = 2123366400) := by
    sorry

  /-- Whenever the function returns a result r, there exist nonnegative integers a, b, c such that r = 2^a * 3^b * 5^c.
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_7 (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r) :
      ∃ a b c : Nat, r.val = 2 ^ a * 3 ^ b * 5 ^ c := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r), ∃ a b c : Nat, r.val = 2 ^ a * 3 ^ b * 5 ^ c) := by
    sorry

  /-- Whenever the function returns a result r, the number of positive integers k with k < r and Ugly(k) is exactly n - 1, where Ugly(k) means that every prime divisor of k is one of 2, 3, and 5.
    Preconditions: n is an integer satisfying 1 <= n <= 1690. -/
  theorem spec_8 (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r) :
      (uglyCountBelow r.val : Int) = n.val - 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n r : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1690)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r), (uglyCountBelow r.val : Int) = n.val - 1) := by
    sorry

  /-- Whenever the function returns r on input n and returns s on input m, r < s.
    Preconditions: n and m are integers satisfying 1 <= n < m <= 1690. -/
  theorem spec_9 (n m r s : Std.I64) (hn_lo : 1 ≤ n.val) (hnm : n.val < m.val)
      (hm_hi : m.val ≤ 1690)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r)
      (hs : Aegis.NthUglyNumber.nth_ugly_number m = ok s) :
      r.val < s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (n m r s : Std.I64) (hn_lo : 1 ≤ n.val) (hnm : n.val < m.val)
        (hm_hi : m.val ≤ 1690)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r)
        (hs : Aegis.NthUglyNumber.nth_ugly_number m = ok s), r.val < s.val) := by
    sorry

  /-- Whenever the function returns r on input n and s on input n+1, r < s and there is no integer u such that r < u < s and Ugly(u), where Ugly(u) means u is a positive integer whose prime divisors are all in {2,3,5}.
    Preconditions: n is an integer satisfying 1 <= n < 1690. -/
  theorem spec_10 (n n1 r s : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val < 1690)
      (hn1 : n1.val = n.val + 1)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r)
      (hs : Aegis.NthUglyNumber.nth_ugly_number n1 = ok s) :
      r.val < s.val ∧ ¬ ∃ u : Int, r.val < u ∧ u < s.val ∧ Ugly u := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n n1 r s : Std.I64) (hn_lo : 1 ≤ n.val) (hn_hi : n.val < 1690)
        (hn1 : n1.val = n.val + 1)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r)
        (hs : Aegis.NthUglyNumber.nth_ugly_number n1 = ok s), r.val < s.val ∧ ¬ ∃ u : Int, r.val < u ∧ u < s.val ∧ Ugly u) := by
    sorry

  /-- Whenever the function returns p on input n-1 and r on input n, p < r, Ugly(r) holds, and every positive integer u with p < u and Ugly(u) satisfies r <= u, where Ugly(x) means that x is a positive integer and every prime divisor of x is one of 2, 3, and 5.
    Preconditions: n is an integer satisfying 2 <= n <= 1690. -/
  theorem spec_11 (n n0 r p : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1690)
      (hn0 : n0.val = n.val - 1)
      (hp : Aegis.NthUglyNumber.nth_ugly_number n0 = ok p)
      (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r) :
      p.val < r.val ∧ Ugly r.val ∧
        ∀ u : Int, p.val < u → Ugly u → r.val ≤ u := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (n n0 r p : Std.I64) (hn_lo : 2 ≤ n.val) (hn_hi : n.val ≤ 1690)
        (hn0 : n0.val = n.val - 1)
        (hp : Aegis.NthUglyNumber.nth_ugly_number n0 = ok p)
        (hr : Aegis.NthUglyNumber.nth_ugly_number n = ok r), p.val < r.val ∧ Ugly r.val ∧
          ∀ u : Int, p.val < u → Ugly u → r.val ≤ u) := by
    sorry

  /-- There exists an integer n with 1 <= n <= 1690 such that the function returns k on input n.
    Preconditions: k is a positive integer satisfying Ugly(k) and k <= 2123366400, where Ugly(k) means that every prime divisor of k is one of 2, 3, and 5. -/
  theorem spec_12 (k : Int) (hk_pos : 0 < k) (hk_ugly : Ugly k) (hk_hi : k ≤ 2123366400) :
      ∃ n r : Std.I64, 1 ≤ n.val ∧ n.val ≤ 1690 ∧
        Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = k := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (k : Int) (hk_pos : 0 < k) (hk_ugly : Ugly k) (hk_hi : k ≤ 2123366400), ∃ n r : Std.I64, 1 ≤ n.val ∧ n.val ≤ 1690 ∧
          Aegis.NthUglyNumber.nth_ugly_number n = ok r ∧ r.val = k) := by
    sorry

  end AegisSpec.NthUglyNumber
