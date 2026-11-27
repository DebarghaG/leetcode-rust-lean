import Aegis.DistinctIntegers.Code.Funs

/-!
# Specifications of `Aegis.DistinctIntegers.distinct_integers`

LeetCode problem `count-distinct-numbers-on-board`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  noncomputable section

  namespace AegisSpec.DistinctIntegers

  def step (n : ℤ) (S : Set ℤ) : Set ℤ :=
    S ∪ {i : ℤ | 1 ≤ i ∧ i ≤ n ∧ ∃ x ∈ S, x % i = 1}

  def board (n : ℤ) : ℕ → Set ℤ
    | 0 => {n}
    | t + 1 => step n (board n t)

  def finalBoard (n : ℤ) : Set ℤ := board n (10 ^ 9)

  /-- The function returns a result r, and r equals the number of distinct integers present on the board after 10^9 days. The board starts as S_0 = {n}; for each day t >= 0, S_{t+1} = S_t union { i : 1 <= i <= n and there exists x in S_t such that x mod i = 1 }. Thus r = |S_{10^9}|.
    Preconditions: n is an integer with 1 <= n <= 100. -/
  theorem spec_1 (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100) :
      ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧
        r.val = ((finalBoard n.val).ncard : ℤ) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100), ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧
          r.val = ((finalBoard n.val).ncard : ℤ)) := by
    sorry

  /-- The function returns a result r, and r = n - 1.
    Preconditions: n is an integer with 2 <= n <= 100. -/
  theorem spec_2 (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100) :
      ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧ r.val = n.val - 1 := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100), ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧ r.val = n.val - 1) := by
    sorry

  /-- The function returns a result r, and r = 1.
    Preconditions: n = 1. -/
  theorem spec_3 (n : Aeneas.Std.I64) (hn : n.val = 1) :
      ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧ r.val = 1 := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 1), ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r ∧ r.val = 1) := by
    sorry

  /-- The function does not fail on any such input: it returns a result. In particular, no arithmetic overflow, out-of-bounds access, or panic occurs.
    Preconditions: n is an integer with 1 <= n <= 100. -/
  theorem spec_4 (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100) :
      ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100), ∃ r, Aegis.DistinctIntegers.distinct_integers n = ok r) := by
    sorry

  /-- Whenever the function returns a result r, 1 <= r <= 100.
    Preconditions: n is an integer with 1 <= n <= 100. -/
  theorem spec_5 (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100) :
      ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r → 1 ≤ r.val ∧ r.val ≤ 100 := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 1 ≤ n.val) (hhi : n.val ≤ 100), ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r → 1 ≤ r.val ∧ r.val ≤ 100) := by
    sorry

  /-- Whenever the function returns a result r, r < n.
    Preconditions: n is an integer with 2 <= n <= 100. -/
  theorem spec_6 (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100) :
      ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r → r.val < n.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100), ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r → r.val < n.val) := by
    sorry

  /-- Whenever the function returns a result r, the set of distinct integers present on the board after 10^9 days, starting from {n} and applying the problem's daily rule, is exactly { k : 2 <= k <= n }; consequently r = n - 1.
    Preconditions: n is an integer with 2 <= n <= 100. -/
  theorem spec_7 (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100) :
      ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r →
        finalBoard n.val = Set.Icc 2 n.val ∧ r.val = n.val - 1 := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hlo : 2 ≤ n.val) (hhi : n.val ≤ 100), ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r →
          finalBoard n.val = Set.Icc 2 n.val ∧ r.val = n.val - 1) := by
    sorry

  /-- Whenever the function returns a result r, the set of distinct integers present on the board after 10^9 days is exactly {1}; consequently r = 1.
    Preconditions: n = 1. -/
  theorem spec_8 (n : Aeneas.Std.I64) (hn : n.val = 1) :
      ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r →
        finalBoard n.val = ({1} : Set ℤ) ∧ r.val = 1 := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n : Aeneas.Std.I64) (hn : n.val = 1), ∀ r, Aegis.DistinctIntegers.distinct_integers n = ok r →
          finalBoard n.val = ({1} : Set ℤ) ∧ r.val = 1) := by
    sorry

  /-- If f(m) and f(n) are the results returned by the function on inputs m and n respectively, then f(m) <= f(n).
    Preconditions: m and n are integers with 1 <= m <= n <= 100. -/
  theorem spec_9 (m n : Aeneas.Std.I64) (hm : 1 ≤ m.val) (hmn : m.val ≤ n.val)
      (hn : n.val ≤ 100) :
      ∀ r s, Aegis.DistinctIntegers.distinct_integers m = ok r →
        Aegis.DistinctIntegers.distinct_integers n = ok s → r.val ≤ s.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (m n : Aeneas.Std.I64) (hm : 1 ≤ m.val) (hmn : m.val ≤ n.val)
        (hn : n.val ≤ 100), ∀ r s, Aegis.DistinctIntegers.distinct_integers m = ok r →
          Aegis.DistinctIntegers.distinct_integers n = ok s → r.val ≤ s.val) := by
    sorry

  /-- If f(n) and f(n-1) are the results returned by the function on inputs n and n-1 respectively, then f(n) = f(n-1) + 1.
    Preconditions: n is an integer with 3 <= n <= 100. -/
  theorem spec_10 (n m : Aeneas.Std.I64) (hn : 3 ≤ n.val) (hhi : n.val ≤ 100)
      (hm : m.val = n.val - 1) :
      ∀ r s, Aegis.DistinctIntegers.distinct_integers n = ok r →
        Aegis.DistinctIntegers.distinct_integers m = ok s → r.val = s.val + 1 := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (n m : Aeneas.Std.I64) (hn : 3 ≤ n.val) (hhi : n.val ≤ 100)
        (hm : m.val = n.val - 1), ∀ r s, Aegis.DistinctIntegers.distinct_integers n = ok r →
          Aegis.DistinctIntegers.distinct_integers m = ok s → r.val = s.val + 1) := by
    sorry

  end AegisSpec.DistinctIntegers
