import Aegis.DifferenceOfSums.Code.Funs

/-!
# Specifications of `Aegis.DifferenceOfSums.difference_of_sums`

LeetCode problem `divisible-and-non-divisible-sums-difference`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.DifferenceOfSums

  def triangular (n : ℤ) : ℤ := n * (n + 1) / 2

  def sumDiv (n m : ℤ) : ℤ :=
    ∑ i ∈ Finset.Ico (1 : ℕ) (n.toNat + 1), if m ∣ (i : ℤ) then (i : ℤ) else 0

  def sumNondiv (n m : ℤ) : ℤ :=
    ∑ i ∈ Finset.Ico (1 : ℕ) (n.toNat + 1), if m ∣ (i : ℤ) then 0 else (i : ℤ)

  def floorDiv (n m : ℤ) : ℤ := n / m

  /-- Whenever the function returns a result r, writing r also for its mathematical integer value, r = (sum over i with 1 <= i <= n and m not dividing i of i) - (sum over i with 1 <= i <= n and m dividing i of i). Here 'm dividing i' means i = m*q for some integer q.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_1 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        r.val = sumNondiv n.val m.val - sumDiv n.val m.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          r.val = sumNondiv n.val m.val - sumDiv n.val m.val) := by
    sorry

  /-- For every n and m satisfying the preconditions, the function returns a result; it does not fail, panic, or overflow.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_2 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∃ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∃ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r) := by
    sorry

  /-- Whenever the function returns r, |r| <= n*(n+1)/2.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_3 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        |r.val| ≤ triangular n.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          |r.val| ≤ triangular n.val) := by
    sorry

  /-- Whenever the function returns r, r and n*(n+1)/2 have the same parity; equivalently, r - n*(n+1)/2 is even.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_4 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        Even (r.val - triangular n.val) := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          Even (r.val - triangular n.val)) := by
    sorry

  /-- Whenever the function returns r, letting q = floor(n/m) be the greatest integer q such that q*m <= n, we have r = n*(n+1)/2 - m*q*(q+1).
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_5 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        r.val = triangular n.val
          - m.val * floorDiv n.val m.val * (floorDiv n.val m.val + 1) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          r.val = triangular n.val
            - m.val * floorDiv n.val m.val * (floorDiv n.val m.val + 1)) := by
    sorry

  /-- Whenever the function returns r, let N = sum over i with 1 <= i <= n and m not dividing i of i and D = sum over i with 1 <= i <= n and m dividing i of i. Then N + D = n*(n+1)/2 and N - D = r.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_6 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        sumNondiv n.val m.val + sumDiv n.val m.val = triangular n.val ∧
          sumNondiv n.val m.val - sumDiv n.val m.val = r.val := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          sumNondiv n.val m.val + sumDiv n.val m.val = triangular n.val ∧
            sumNondiv n.val m.val - sumDiv n.val m.val = r.val) := by
    sorry

  /-- For every n and m satisfying the preconditions, if m <= n, then whenever the function returns r, r <= n*(n+1)/2 - 2*m.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_7 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
      (hmn : m.val ≤ n.val) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        r.val ≤ triangular n.val - 2 * m.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
        (hmn : m.val ≤ n.val), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          r.val ≤ triangular n.val - 2 * m.val) := by
    sorry

  /-- For every n and m satisfying the preconditions, if m > 1, then whenever the function returns r, r >= 2 - n*(n+1)/2.
    Preconditions: n and m are 64-bit signed integers whose mathematical integer values satisfy 1 <= n <= 1000 and 1 <= m <= 1000. -/
  theorem spec_8 (n m : Std.I64)
      (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
      (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
      (hm : 1 < m.val) :
      ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
        2 - triangular n.val ≤ r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (n m : Std.I64)
        (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 1000)
        (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
        (hm : 1 < m.val), ∀ r, Aegis.DifferenceOfSums.difference_of_sums n m = ok r →
          2 - triangular n.val ≤ r.val) := by
    sorry

  end AegisSpec.DifferenceOfSums
