import Aegis.EatenApples.Code.Funs

/-!
# Specifications of `Aegis.EatenApples.eaten_apples`

LeetCode problem `maximum-number-of-eaten-apples`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.EatenApples

def getZ (l : List Std.I64) (i : ℤ) : ℤ :=
  if 0 ≤ i then (l.getD i.toNat 0#i64).val else 0

lemma getZ_of_lt {l : List Std.I64} {i : ℕ} (h : i < l.length) :
    getZ l (i : ℤ) = (l[i]).val := by
  simp only [getZ, Int.toNat_natCast]
  rw [ite_eq_left (by omega : (0 : ℤ) ≤ (i : ℤ))]
  simp only [List.getD, List.getElem?_eq_getElem h, Option.getD_some]

lemma getZ_of_neg {l : List Std.I64} {i : ℤ} (h : i < 0) : getZ l i = 0 := by
  simp only [getZ]
  rw [ite_eq_right (by omega : ¬ (0 ≤ i))]

def posCount (apples : List Std.I64) : ℕ :=
  apples.countP (fun a => 0 < a.val)

def sumApples (apples : List Std.I64) : ℤ :=
  (apples.map (fun a => a.val)).sum

def reachable (days : List Std.I64) : Set ℤ :=
  {d : ℤ | 0 ≤ d ∧ ∃ i : ℕ, i < days.length ∧ (i : ℤ) ≤ d ∧ d < (i : ℤ) + getZ days (i : ℤ)}

def ValidInput (apples days : Slice Std.I64) : Prop :=
  apples.val.length = days.val.length ∧
  1 ≤ apples.val.length ∧
  apples.val.length ≤ 20000 ∧
  ∀ i : ℕ, i < apples.val.length →
    0 ≤ getZ apples.val (i : ℤ) ∧ getZ apples.val (i : ℤ) ≤ 20000 ∧
    0 ≤ getZ days.val (i : ℤ) ∧ getZ days.val (i : ℤ) ≤ 20000 ∧
    (getZ days.val (i : ℤ) = 0 ↔ getZ apples.val (i : ℤ) = 0)

def Feasible (apples days : List Std.I64) (n : ℕ) (S : Finset (ℤ × ℤ)) : Prop :=
  (∀ p ∈ S, 0 ≤ p.1 ∧ p.1 < (n : ℤ) ∧ 0 ≤ p.2) ∧
  (∀ p ∈ S, p.1 ≤ p.2 ∧ p.2 < p.1 + getZ days p.1) ∧
  (∀ i : ℕ, i < n → ((S.filter (fun p => p.1 = (i : ℤ))).card : ℤ) ≤ getZ apples (i : ℤ)) ∧
  (∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q)

/-- The function returns a result r. Call a set S of ordered pairs (i,d) with i,d integers a feasible eating plan if: (1) every pair in S has 0 <= i < n and d >= 0; (2) i <= d < i + days[i] for every (i,d) in S; (3) for every i, the number of pairs in S whose first component is i is at most apples[i]; and (4) the second components d of all pairs in S are pairwise distinct. Then r is the maximum of |S| over all feasible eating plans S.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_1 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        (∃ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S ∧
          (S.card : ℤ) = r.val) ∧
        ∀ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S →
          (S.card : ℤ) ≤ r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        (∃ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S ∧
          (S.card : ℤ) = r.val) ∧
        ∀ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S →
          (S.card : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r; in particular, on every input satisfying the preconditions it does not fail, panic, overflow, or access an out-of-bounds index.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_2 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64, Aegis.EatenApples.eaten_apples apples days = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64, Aegis.EatenApples.eaten_apples apples days = ok r) := by
  sorry

/-- The function returns a result r and 0 <= r <= sum_{i=0}^{n-1} apples[i].
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_3 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        0 ≤ r.val ∧ r.val ≤ sumApples apples.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        0 ≤ r.val ∧ r.val ≤ sumApples apples.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if apples[i] = 0 for every i with 0 <= i < n.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_4 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        (r.val = 0 ↔ ∀ i : ℕ, i < apples.val.length → getZ apples.val (i : ℤ) = 0) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        (r.val = 0 ↔ ∀ i : ℕ, i < apples.val.length → getZ apples.val (i : ℤ) = 0)) := by
  sorry

/-- The function returns a result r and r >= |{ i : 0 <= i < n and apples[i] > 0 }|.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_5 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧ (posCount apples.val : ℤ) ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧ (posCount apples.val : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= |U|, where U = { d : d is an integer, d >= 0, and there exists i with 0 <= i < n and i <= d < i + days[i] }.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_6 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val ≤ ((reachable days.val).ncard : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val ≤ ((reachable days.val).ncard : ℤ)) := by
  sorry

/-- The function returns a result r and there exists a set S of ordered pairs (i,d) with i,d integers such that: every (i,d) in S has 0 <= i < n and d >= 0; i <= d < i + days[i] for every (i,d) in S; for every i, the number of pairs in S with first component i is at most apples[i]; the second components of all pairs in S are pairwise distinct; and |S| = r.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_7 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        ∃ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S ∧
          (S.card : ℤ) = r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        ∃ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S ∧
          (S.card : ℤ) = r.val) := by
  sorry

/-- The function returns a result r and every set S of ordered pairs (i,d) with i,d integers satisfying the following four conditions has |S| <= r: every (i,d) in S has 0 <= i < n and d >= 0; i <= d < i + days[i] for every (i,d) in S; for every i, the number of pairs in S with first component i is at most apples[i]; and the second components of all pairs in S are pairwise distinct.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_8 (apples days : Slice Std.I64) (h : ValidInput apples days) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        ∀ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S →
          (S.card : ℤ) ≤ r.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        ∀ S : Finset (ℤ × ℤ), Feasible apples.val days.val apples.val.length S →
          (S.card : ℤ) ≤ r.val) := by
  sorry

/-- The function returns a result r and r = min(apples[0], days[0]).
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, n = 1, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_9 (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hn : apples.val.length = 1) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = min (getZ apples.val 0) (getZ days.val 0) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hn : apples.val.length = 1), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = min (getZ apples.val 0) (getZ days.val 0)) := by
  sorry

/-- The function returns a result r and r = |{ i : 0 <= i < n and apples[i] > 0 }|.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, days[i] = 0 if and only if apples[i] = 0, and days[i] <= 1. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_10 (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hday : ∀ i : ℕ, i < apples.val.length → getZ days.val (i : ℤ) ≤ 1) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧ r.val = (posCount apples.val : ℤ) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hday : ∀ i : ℕ, i < apples.val.length → getZ days.val (i : ℤ) ≤ 1), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧ r.val = (posCount apples.val : ℤ)) := by
  sorry

/-- The function returns a result r and r = min(apples[k], days[k]).
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. Also assume there exists k with 0 <= k < n such that apples[k] > 0 and apples[i] = 0 for every i with 0 <= i < n and i != k. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_11 (apples days : Slice Std.I64) (h : ValidInput apples days)
    (k : ℕ) (hk : k < apples.val.length) (hkpos : 0 < getZ apples.val (k : ℤ))
    (hrest : ∀ i : ℕ, i < apples.val.length → i ≠ k → getZ apples.val (i : ℤ) = 0) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = min (getZ apples.val (k : ℤ)) (getZ days.val (k : ℤ)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days)
    (k : ℕ) (hk : k < apples.val.length) (hkpos : 0 < getZ apples.val (k : ℤ))
    (hrest : ∀ i : ℕ, i < apples.val.length → i ≠ k → getZ apples.val (i : ℤ) = 0), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = min (getZ apples.val (k : ℤ)) (getZ days.val (k : ℤ))) := by
  sorry

/-- The function returns results r and r2 on inputs (apples, days) and (apples2, days2), respectively, and r2 = r.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. Let m be an integer with n <= m <= 20000, and let apples2 and days2 be arrays of length m such that apples2[i] = apples[i] and days2[i] = days[i] for 0 <= i < n, apples2[i] = 0 and days2[i] = 0 for n <= i < m, and the same value bounds and the condition days2[i] = 0 if and only if apples2[i] = 0 hold. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_12 (apples days apples2 days2 : Slice Std.I64) (h : ValidInput apples days)
    (m : ℕ) (hm1 : apples.val.length ≤ m) (hm2 : m ≤ 20000)
    (h2 : ValidInput apples2 days2)
    (hlen2 : apples2.val.length = m) (hlen3 : days2.val.length = m)
    (hagree : ∀ i : ℕ, i < apples.val.length →
      getZ apples2.val (i : ℤ) = getZ apples.val (i : ℤ) ∧
      getZ days2.val (i : ℤ) = getZ days.val (i : ℤ))
    (hpad : ∀ i : ℕ, apples.val.length ≤ i → i < m →
      getZ apples2.val (i : ℤ) = 0 ∧ getZ days2.val (i : ℤ) = 0) :
    ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days2 = ok r2 ∧ r2.val = r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (apples days apples2 days2 : Slice Std.I64) (h : ValidInput apples days)
    (m : ℕ) (hm1 : apples.val.length ≤ m) (hm2 : m ≤ 20000)
    (h2 : ValidInput apples2 days2)
    (hlen2 : apples2.val.length = m) (hlen3 : days2.val.length = m)
    (hagree : ∀ i : ℕ, i < apples.val.length →
      getZ apples2.val (i : ℤ) = getZ apples.val (i : ℤ) ∧
      getZ days2.val (i : ℤ) = getZ days.val (i : ℤ))
    (hpad : ∀ i : ℕ, apples.val.length ≤ i → i < m →
      getZ apples2.val (i : ℤ) = 0 ∧ getZ days2.val (i : ℤ) = 0), ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days2 = ok r2 ∧ r2.val = r.val) := by
  sorry

/-- The function returns results r and r2 on inputs (apples, days) and (apples2, days), respectively, and r2 >= r.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. Let apples2 be another array of length n such that for every i with 0 <= i < n, apples[i] <= apples2[i] <= 20000, and days[i] = 0 if and only if apples2[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_13 (apples days apples2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : apples2.val.length = apples.val.length)
    (hmono : ∀ i : ℕ, i < apples.val.length →
      getZ apples.val (i : ℤ) ≤ getZ apples2.val (i : ℤ) ∧ getZ apples2.val (i : ℤ) ≤ 20000)
    (hiff : ∀ i : ℕ, i < apples.val.length →
      (getZ days.val (i : ℤ) = 0 ↔ getZ apples2.val (i : ℤ) = 0)) :
    ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days = ok r2 ∧ r.val ≤ r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (apples days apples2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : apples2.val.length = apples.val.length)
    (hmono : ∀ i : ℕ, i < apples.val.length →
      getZ apples.val (i : ℤ) ≤ getZ apples2.val (i : ℤ) ∧ getZ apples2.val (i : ℤ) ≤ 20000)
    (hiff : ∀ i : ℕ, i < apples.val.length →
      (getZ days.val (i : ℤ) = 0 ↔ getZ apples2.val (i : ℤ) = 0)), ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days = ok r2 ∧ r.val ≤ r2.val) := by
  sorry

/-- The function returns results r and r2 on inputs (apples, days) and (apples, days2), respectively, and r2 >= r.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. Let days2 be another array of length n such that for every i with 0 <= i < n, days[i] <= days2[i] <= 20000, and days2[i] = 0 if and only if apples[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_14 (apples days days2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : days2.val.length = apples.val.length)
    (hmono : ∀ i : ℕ, i < apples.val.length →
      getZ days.val (i : ℤ) ≤ getZ days2.val (i : ℤ) ∧ getZ days2.val (i : ℤ) ≤ 20000)
    (hiff : ∀ i : ℕ, i < apples.val.length →
      (getZ days2.val (i : ℤ) = 0 ↔ getZ apples.val (i : ℤ) = 0)) :
    ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples days2 = ok r2 ∧ r.val ≤ r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (apples days days2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : days2.val.length = apples.val.length)
    (hmono : ∀ i : ℕ, i < apples.val.length →
      getZ days.val (i : ℤ) ≤ getZ days2.val (i : ℤ) ∧ getZ days2.val (i : ℤ) ≤ 20000)
    (hiff : ∀ i : ℕ, i < apples.val.length →
      (getZ days2.val (i : ℤ) = 0 ↔ getZ apples.val (i : ℤ) = 0)), ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples days2 = ok r2 ∧ r.val ≤ r2.val) := by
  sorry

/-- The function returns a result r and r = |U|, where U = { d : d is an integer, d >= 0, and there exists i with 0 <= i < n and i <= d < i + days[i] }.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, days[i] = 0 if and only if apples[i] = 0, and apples[i] >= days[i]. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_15 (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hdom : ∀ i : ℕ, i < apples.val.length → getZ days.val (i : ℤ) ≤ getZ apples.val (i : ℤ)) :
    ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = ((reachable days.val).ncard : ℤ) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (apples days : Slice Std.I64) (h : ValidInput apples days)
    (hdom : ∀ i : ℕ, i < apples.val.length → getZ days.val (i : ℤ) ≤ getZ apples.val (i : ℤ)), ∃ r : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        r.val = ((reachable days.val).ncard : ℤ)) := by
  sorry

/-- The function returns results r and r2 on inputs (apples, days) and (apples2, days), respectively, and r2 = r.
  Preconditions: Let n = len(apples). Assume len(apples) = len(days) = n, 1 <= n <= 20000, and for every i with 0 <= i < n, 0 <= apples[i] <= 20000, 0 <= days[i] <= 20000, and days[i] = 0 if and only if apples[i] = 0. Define apples2[i] = min(apples[i], days[i]) for every i with 0 <= i < n. Then apples2 also satisfies the same value bounds and the condition days[i] = 0 if and only if apples2[i] = 0. All indices and array lengths are mathematical integers; the i64 inputs are taken at their integer values. -/
theorem spec_16 (apples days apples2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : apples2.val.length = apples.val.length)
    (hmin : ∀ i : ℕ, i < apples.val.length →
      getZ apples2.val (i : ℤ) = min (getZ apples.val (i : ℤ)) (getZ days.val (i : ℤ))) :
    ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days = ok r2 ∧ r2.val = r.val := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (apples days apples2 : Slice Std.I64) (h : ValidInput apples days)
    (hlen : apples2.val.length = apples.val.length)
    (hmin : ∀ i : ℕ, i < apples.val.length →
      getZ apples2.val (i : ℤ) = min (getZ apples.val (i : ℤ)) (getZ days.val (i : ℤ))), ∃ r r2 : Std.I64,
      Aegis.EatenApples.eaten_apples apples days = ok r ∧
        Aegis.EatenApples.eaten_apples apples2 days = ok r2 ∧ r2.val = r.val) := by
  sorry

end AegisSpec.EatenApples
