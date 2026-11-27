import Aegis.CountOfArrays.Code.Funs

/-!
# Specifications of `Aegis.CountOfArrays.count_of_arrays`

LeetCode problem `find-the-number-of-k-even-arrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open scoped BigOperators

namespace AegisSpec.CountOfArrays

abbrev stepEven (a b : ℤ) : Prop := Even (a * b - a - b)

def curIdx {N : ℕ} (i : Fin (N - 1)) : Fin N := ⟨i.val, by omega⟩

def nextIdx {N : ℕ} (i : Fin (N - 1)) : Fin N := ⟨i.val + 1, by omega⟩

def valueSet (m : ℤ) : Finset ℤ := Finset.image (fun i : ℕ => (i : ℤ) + 1) (Finset.range m.toNat)

noncomputable def C (n m k : ℤ) : ℤ :=
  ((Fintype.piFinset (fun _ : Fin n.toNat => valueSet m)).filter
      (fun arr =>
        (Finset.univ.filter fun i : Fin (n.toNat - 1) =>
            stepEven (arr (curIdx i)) (arr (nextIdx i))).card
          = k.toNat)).card

def fibSpec : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | t + 2 => fibSpec (t + 1) + fibSpec t

def ibinom (x y : ℤ) : ℤ :=
  if 0 ≤ y ∧ y ≤ x then (x.toNat.choose y.toNat : ℤ) else 0

def closedForm (n m k : ℤ) : ℤ :=
  let e := m / 2
  let o := m - e
  (if k = 0 then o ^ n.toNat else 0) +
    ∑ a ∈ Finset.Icc 1 n.toNat,
      e ^ a * o ^ (n.toNat - a) * ibinom (a - 1) k * ibinom (n - a + 1) (a - k)

/-- Let C(n,m,k) be the number of integer arrays arr of length n such that 1 <= arr[i] <= m for every i with 0 <= i < n, and such that the set { i | 0 <= i < n-1 and ((arr[i] * arr[i+1]) - arr[i] - arr[i+1]) is even } has exactly k elements. Whenever count_of_arrays n m k returns Result.ok r, r is the unique integer satisfying 0 <= r < 1000000007 and r = C(n,m,k) modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_1 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
      0 ≤ r.val ∧ r.val < 1000000007 ∧ r.val % 1000000007 = C n.val m.val k.val % 1000000007 := by
  sorry

theorem spec_1_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
      0 ≤ r.val ∧ r.val < 1000000007 ∧ r.val % 1000000007 = C n.val m.val k.val % 1000000007) := by
  sorry

/-- For every n, m, k satisfying the preconditions, the call count_of_arrays n m k does not fail: there exists an integer r such that count_of_arrays n m k returns Result.ok r; in particular there is no panic, out-of-bounds access, or machine-integer overflow.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_2 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∃ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∃ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r) := by
  sorry

/-- Whenever count_of_arrays n m k returns Result.ok r and n = 1 (so, under the preconditions, k = 0), r = m modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_3 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → n.val = 1 →
      r.val % 1000000007 = m.val % 1000000007 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → n.val = 1 →
      r.val % 1000000007 = m.val % 1000000007) := by
  sorry

/-- Whenever count_of_arrays n m k returns Result.ok r and m = 1, r = 1 if k = 0, and r = 0 if k > 0.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_4 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → m.val = 1 →
      (k.val = 0 → r.val % 1000000007 = 1) ∧ (0 < k.val → r.val % 1000000007 = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → m.val = 1 →
      (k.val = 0 → r.val % 1000000007 = 1) ∧ (0 < k.val → r.val % 1000000007 = 0)) := by
  sorry

/-- Whenever count_of_arrays n m k returns Result.ok r, n >= 2, and k = n - 1, r = (floor(m/2))^n modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_5 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → 2 ≤ n.val →
      k.val = n.val - 1 →
        r.val % 1000000007 = ((m.val / 2) ^ n.val.toNat) % 1000000007 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → 2 ≤ n.val →
      k.val = n.val - 1 →
        r.val % 1000000007 = ((m.val / 2) ^ n.val.toNat) % 1000000007) := by
  sorry

/-- Whenever count_of_arrays n m k returns Result.ok r, n = 2, and k = 0, r = (m^2 - (floor(m/2))^2) modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_6 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → n.val = 2 → k.val = 0 →
      r.val % 1000000007 = (m.val ^ 2 - (m.val / 2) ^ 2) % 1000000007 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → n.val = 2 → k.val = 0 →
      r.val % 1000000007 = (m.val ^ 2 - (m.val / 2) ^ 2) % 1000000007) := by
  sorry

/-- For fixed n and m, if for every j with 0 <= j <= n-1 the call count_of_arrays n m j returns Result.ok r_j, then (sum_{j=0}^{n-1} r_j) modulo 1000000007 equals (m^n) modulo 1000000007.
  Preconditions: n and m are integer values represented by Std.I64 satisfying 1 <= n <= 750 and 1 <= m <= 1000. -/
theorem spec_7 {n m : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (ρ : ℤ → ℤ)
    (hρ : ∀ j : Std.I64, 0 ≤ j.val → j.val ≤ n.val - 1 →
      ∃ x : Std.I64, Aegis.CountOfArrays.count_of_arrays n m j = ok x ∧ x.val = ρ j.val) :
    (∑ j ∈ Finset.range n.val.toNat, ρ (j : ℤ)) % 1000000007
      = (m.val ^ n.val.toNat) % 1000000007 := by
  sorry

theorem spec_7_neg :
    ¬ (∀ {n m : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (ρ : ℤ → ℤ)
    (hρ : ∀ j : Std.I64, 0 ≤ j.val → j.val ≤ n.val - 1 →
      ∃ x : Std.I64, Aegis.CountOfArrays.count_of_arrays n m j = ok x ∧ x.val = ρ j.val), (∑ j ∈ Finset.range n.val.toNat, ρ (j : ℤ)) % 1000000007
      = (m.val ^ n.val.toNat) % 1000000007) := by
  sorry

/-- For every n, m, k satisfying the preconditions, let C(n,m,k) be the number defined in spec_1. Then C(n,m,k) > 0 if and only if m >= 2 or k = 0. Consequently, whenever count_of_arrays n m k returns Result.ok r and m = 1 with k > 0, r = 0; in all other cases r is the residue modulo 1000000007 of a positive integer.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_8 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    (0 < C n.val m.val k.val ↔ 2 ≤ m.val ∨ k.val = 0) ∧
      ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
        (m.val = 1 ∧ 0 < k.val → r.val = 0) ∧
          (¬(m.val = 1 ∧ 0 < k.val) → 0 < C n.val m.val k.val ∧
            r.val % 1000000007 = C n.val m.val k.val % 1000000007) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), (0 < C n.val m.val k.val ↔ 2 ≤ m.val ∨ k.val = 0) ∧
      ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
        (m.val = 1 ∧ 0 < k.val → r.val = 0) ∧
          (¬(m.val = 1 ∧ 0 < k.val) → 0 < C n.val m.val k.val ∧
            r.val % 1000000007 = C n.val m.val k.val % 1000000007)) := by
  sorry

/-- Let F be defined by F_1 = 1, F_2 = 1, and F_t = F_{t-1} + F_{t-2} for t >= 3. Whenever count_of_arrays n m k returns Result.ok r, m = 2, and k = 0, r = F_{n+2} modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_9 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → m.val = 2 →
      k.val = 0 → r.val % 1000000007 = fibSpec (n.val.toNat + 2) % 1000000007 := by
  sorry

theorem spec_9_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → m.val = 2 →
      k.val = 0 → r.val % 1000000007 = fibSpec (n.val.toNat + 2) % 1000000007) := by
  sorry

/-- Whenever count_of_arrays n m k returns Result.ok r, n >= 3, and k = n - 2, r = (2 * (m - floor(m/2)) * (floor(m/2))^(n-1)) modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_10 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → 3 ≤ n.val →
      k.val = n.val - 2 →
        r.val % 1000000007
          = (2 * (m.val - m.val / 2) * (m.val / 2) ^ (n.val.toNat - 1)) % 1000000007 := by
  sorry

theorem spec_10_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r → 3 ≤ n.val →
      k.val = n.val - 2 →
        r.val % 1000000007
          = (2 * (m.val - m.val / 2) * (m.val / 2) ^ (n.val.toNat - 1)) % 1000000007) := by
  sorry

/-- Let C(n,m,k) be as in spec_1, let e = floor(m/2), o = m - e, and adopt the convention binom(x,y)=0 when y<0 or y>x. Then C(n,m,k) = (if k = 0 then o^n else 0) + sum_{a=1}^{n} e^a o^{n-a} binom(a-1,k) binom(n-a+1,a-k). This is an integer identity, and hence the returned residue is this value modulo 1000000007.
  Preconditions: n, m, k are integer values represented by Std.I64 satisfying 1 <= n <= 750, 1 <= m <= 1000, and 0 <= k <= n - 1. -/
theorem spec_11 {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1) :
    C n.val m.val k.val = closedForm n.val m.val k.val ∧
      ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
        r.val % 1000000007 = closedForm n.val m.val k.val % 1000000007 := by
  sorry

theorem spec_11_neg :
    ¬ (∀ {n m k : Std.I64}
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 750)
    (hm_lo : 1 ≤ m.val) (hm_hi : m.val ≤ 1000)
    (hk_lo : 0 ≤ k.val) (hk_hi : k.val ≤ n.val - 1), C n.val m.val k.val = closedForm n.val m.val k.val ∧
      ∀ r : Std.I64, Aegis.CountOfArrays.count_of_arrays n m k = ok r →
        r.val % 1000000007 = closedForm n.val m.val k.val % 1000000007) := by
  sorry

end AegisSpec.CountOfArrays
