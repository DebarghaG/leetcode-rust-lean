import Aegis.SumBase.Code.Funs

/-!
# Specifications of `Aegis.SumBase.sum_base`

LeetCode problem `sum-of-digits-in-base-k`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.SumBase

def digitSum (k n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log k n + 1), n / k ^ i % k

variable (n k : Std.I64)

/-- Let m >= 0 and d_0, d_1, ..., d_m be the unique integers such that 0 <= d_i < k for every i with 0 <= i <= m, d_m != 0, and n = sum_{i=0}^m d_i * k^i. The function returns a result r and r = sum_{i=0}^m d_i.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_1 (m : ℕ) (d : ℕ → ℤ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hd : ∀ i ≤ m, 0 ≤ d i ∧ d i < k.val)
    (hdm : d m ≠ 0)
    (hrep : n.val = ∑ i ∈ Finset.range (m + 1), d i * k.val ^ i) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val = ∑ i ∈ Finset.range (m + 1), d i := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (m : ℕ) (d : ℕ → ℤ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hd : ∀ i ≤ m, 0 ≤ d i ∧ d i < k.val)
    (hdm : d m ≠ 0)
    (hrep : n.val = ∑ i ∈ Finset.range (m + 1), d i * k.val ^ i), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val = ∑ i ∈ Finset.range (m + 1), d i) := by
  sorry

/-- The function returns a result r (it does not fail with overflow, panic, or out-of-bounds access).
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_2
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r) := by
  sorry

/-- The function returns a result r and 1 <= r.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_3
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ 1 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ 1 ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= n.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_4
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ n.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ n.val) := by
  sorry

/-- The function returns a result r. Let L be the unique positive integer such that k^(L-1) <= n < k^L (the number of base-k digits of n). Then r <= (k - 1) * L.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_5 (L : ℕ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hLpos : 0 < L)
    (hLlo : k.val ^ (L - 1) ≤ n.val)
    (hLhi : n.val < k.val ^ L) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ (k.val - 1) * (L : ℤ) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (L : ℕ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hLpos : 0 < L)
    (hLlo : k.val ^ (L - 1) ≤ n.val)
    (hLhi : n.val < k.val ^ L), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ (k.val - 1) * (L : ℤ)) := by
  sorry

/-- The function returns a result r and r <= 18.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_6
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ 18 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val ≤ 18) := by
  sorry

/-- The function returns a result r, and r = n if and only if n < k.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_7
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ (r.val = n.val ↔ n.val < k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ (r.val = n.val ↔ n.val < k.val)) := by
  sorry

/-- The function returns a result r, and r = 1 if and only if there exists an integer m >= 0 such that n = k^m.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_8
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ (r.val = 1 ↔ ∃ m : ℕ, n.val = k.val ^ m) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ (r.val = 1 ↔ ∃ m : ℕ, n.val = k.val ^ m)) := by
  sorry

/-- For the unique such m, the function returns a result r and r = m * (k - 1).
  Preconditions: 1 <= n <= 100, 2 <= k <= 10, and there exists an integer m >= 2 such that n = k^m - 1. -/
theorem spec_9 (m : ℕ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hm : 2 ≤ m)
    (hnm : n.val = k.val ^ m - 1) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val = (m : ℤ) * (k.val - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (m : ℕ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (hm : 2 ≤ m)
    (hnm : n.val = k.val ^ m - 1), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧ r.val = (m : ℤ) * (k.val - 1)) := by
  sorry

/-- The function returns a result r and r is congruent to n modulo k - 1; equivalently, r mod (k - 1) = n mod (k - 1).
  Preconditions: 1 <= n <= 100 and 3 <= k <= 10. -/
theorem spec_10
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 3 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val % (k.val - 1) = n.val % (k.val - 1) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 3 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val % (k.val - 1) = n.val % (k.val - 1)) := by
  sorry

/-- Let S_k(a) be the sum of the base-k digits of a (i.e., if a = sum_{i=0}^t c_i * k^i with 0 <= c_i < k and c_t != 0, then S_k(a) = sum_{i=0}^t c_i). The function returns a result r and r = S_k(a) + b.
  Preconditions: 1 <= n <= 100, 2 <= k <= 10, and n = a * k + b for some integers a >= 1 and 0 <= b < k. -/
theorem spec_11 (a b : ℤ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b < k.val)
    (hnab : n.val = a * k.val + b) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val = (digitSum k.val.toNat a.toNat : ℤ) + b := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (a b : ℤ)
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10)
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b < k.val)
    (hnab : n.val = a * k.val + b), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      r.val = (digitSum k.val.toNat a.toNat : ℤ) + b) := by
  sorry

/-- The function returns a result r, and r is the smallest integer t >= 0 for which there exist integers e_1, ..., e_t with e_j >= 0 for all j and n = sum_{j=1}^t k^{e_j}.
  Preconditions: 1 <= n <= 100 and 2 <= k <= 10. -/
theorem spec_12
    (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10) :
    ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      ∃ t : ℕ, (∃ e : Fin t → ℕ, n.val = ∑ j : Fin t, k.val ^ (e j)) ∧
        r.val = (t : ℤ) ∧
        (∀ s : ℕ, (∃ e : Fin s → ℕ, n.val = ∑ j : Fin s, k.val ^ (e j)) →
          (t : ℤ) ≤ (s : ℤ)) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (hn : 1 ≤ n.val) (hn' : n.val ≤ 100) (hk : 2 ≤ k.val) (hk' : k.val ≤ 10), ∃ r, Aegis.SumBase.sum_base n k = ok r ∧
      ∃ t : ℕ, (∃ e : Fin t → ℕ, n.val = ∑ j : Fin t, k.val ^ (e j)) ∧
        r.val = (t : ℤ) ∧
        (∀ s : ℕ, (∃ e : Fin s → ℕ, n.val = ∑ j : Fin s, k.val ^ (e j)) →
          (t : ℤ) ≤ (s : ℤ))) := by
  sorry

end AegisSpec.SumBase
