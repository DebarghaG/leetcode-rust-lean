import Aegis.FindMinimumTime.Code.Funs

/-!
# Specifications of `Aegis.FindMinimumTime.find_minimum_time`

LeetCode problem `minimum-time-to-break-locks-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.FindMinimumTime

namespace AegisSpec.FindMinimumTime

def ceilDiv (a b : ℤ) : ℤ := max 0 ((a + b - 1) / b)

def permCost (l : List Std.I64) (k : ℤ) (p : Fin l.length → Fin l.length) : ℤ :=
  ∑ j : Fin l.length, ceilDiv (l.get (p j)).val (1 + ((j : ℕ) : ℤ) * k)

def costSum (l : List Std.I64) (d : ℤ) : ℤ :=
  ∑ i : Fin l.length, ceilDiv (l.get i).val d

def minVal : List Std.I64 → ℤ
  | [] => 0
  | x :: t => t.foldr (fun y acc => min y.val acc) x.val

/-- The function returns a result r, and r is the minimum, over all permutations p = (p(0),...,p(n-1)) of the index set {0,...,n-1}, of T(p) = sum_{j=0}^{n-1} ceil(strength[p(j)] / (1 + j*k)), where ceil(a/b) for positive integer b and integer a is the least integer t >= 0 with t*b >= a.
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_1 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∃ r : Std.I64,
      find_minimum_time strength k = ok r ∧
      (∃ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p ∧ r.val = permCost strength.val k.val p) ∧
      (∀ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p → r.val ≤ permCost strength.val k.val p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∃ r : Std.I64,
      find_minimum_time strength k = ok r ∧
      (∃ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p ∧ r.val = permCost strength.val k.val p) ∧
      (∀ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p → r.val ≤ permCost strength.val k.val p)) := by
  sorry

/-- Whenever the function returns a result r, r >= min_{0 <= i < n} strength[i] + (n - 1).
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_2 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      minVal strength.val + ((n : ℤ) - 1) ≤ r.val := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      minVal strength.val + ((n : ℤ) - 1) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r >= sum_{i=0}^{n-1} ceil(strength[i] / (1 + (n-1)*k)), where ceil(a/b) is the least integer t >= 0 with t*b >= a.
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_3 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      costSum strength.val (1 + ((n : ℤ) - 1) * k.val) ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      costSum strength.val (1 + ((n : ℤ) - 1) * k.val) ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= sum_{i=0}^{n-1} ceil(strength[i] / (1 + i*k)), where ceil(a/b) is the least integer t >= 0 with t*b >= a.
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_4 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val ≤ ∑ i : Fin strength.val.length,
        ceilDiv (strength.val.get i).val (1 + ((i : ℕ) : ℤ) * k.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val ≤ ∑ i : Fin strength.val.length,
        ceilDiv (strength.val.get i).val (1 + ((i : ℕ) : ℤ) * k.val)) := by
  sorry

/-- For every index m with 0 <= m < n and strength[m] = min_{0 <= i < n} strength[i], whenever the function returns a result r, r <= strength[m] + sum_{0 <= i < n, i != m} ceil(strength[i] / (1 + k)), where ceil(a/b) is the least integer t >= 0 with t*b >= a.
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_5 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (m : ℕ) (hm : m < n) (hmin : strength.val[m].val = minVal strength.val) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val ≤ strength.val[m].val +
        ∑ i : Fin strength.val.length,
          if (i : ℕ) = m then 0 else ceilDiv (strength.val.get i).val (1 + k.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (m : ℕ) (hm : m < n) (hmin : strength.val[m].val = minVal strength.val), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val ≤ strength.val[m].val +
        ∑ i : Fin strength.val.length,
          if (i : ℕ) = m then 0 else ceilDiv (strength.val.get i).val (1 + k.val)) := by
  sorry

/-- If find_minimum_time(a,k) returns r_a and find_minimum_time(b,k) returns r_b, then r_a = r_b.
  Preconditions: Let a and b be two strength slices of the same length n. Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= a[i] <= 1000000 and 1 <= b[i] <= 1000000. Assume b is a permutation of a, meaning there is a bijection sigma on {0,...,n-1} with b[j] = a[sigma(j)] for every j. -/
theorem spec_6 (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (ha : a.val.length = n) (hb : b.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hsa : ∀ i : Fin n, 1 ≤ a.val[i.val].val ∧ a.val[i.val].val ≤ 1000000)
    (hsb : ∀ i : Fin n, 1 ≤ b.val[i.val].val ∧ b.val[i.val].val ≤ 1000000)
    (hperm : ∃ σ : Fin n → Fin n, Function.Bijective σ ∧
      ∀ j : Fin n, b.val.get ⟨(j : ℕ), by omega⟩ = a.val.get ⟨(σ j : ℕ), by omega⟩)
    (ra rb : Std.I64)
    (hra : find_minimum_time a k = ok ra) (hrb : find_minimum_time b k = ok rb) :
    ra.val = rb.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (ha : a.val.length = n) (hb : b.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hsa : ∀ i : Fin n, 1 ≤ a.val[i.val].val ∧ a.val[i.val].val ≤ 1000000)
    (hsb : ∀ i : Fin n, 1 ≤ b.val[i.val].val ∧ b.val[i.val].val ≤ 1000000)
    (hperm : ∃ σ : Fin n → Fin n, Function.Bijective σ ∧
      ∀ j : Fin n, b.val.get ⟨(j : ℕ), by omega⟩ = a.val.get ⟨(σ j : ℕ), by omega⟩)
    (ra rb : Std.I64)
    (hra : find_minimum_time a k = ok ra) (hrb : find_minimum_time b k = ok rb), ra.val = rb.val) := by
  sorry

/-- If find_minimum_time(a,k) returns r_a and find_minimum_time(b,k) returns r_b, then r_a <= r_b.
  Preconditions: Let a and b be two strength slices of the same length n. Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= a[i] <= b[i] <= 1000000. -/
theorem spec_7 (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (ha : a.val.length = n) (hb : b.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n,
      1 ≤ a.val[i.val].val ∧ a.val[i.val].val ≤ b.val[i.val].val ∧
        b.val[i.val].val ≤ 1000000)
    (ra rb : Std.I64)
    (hra : find_minimum_time a k = ok ra) (hrb : find_minimum_time b k = ok rb) :
    ra.val ≤ rb.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (a b : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (ha : a.val.length = n) (hb : b.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n,
      1 ≤ a.val[i.val].val ∧ a.val[i.val].val ≤ b.val[i.val].val ∧
        b.val[i.val].val ≤ 1000000)
    (ra rb : Std.I64)
    (hra : find_minimum_time a k = ok ra) (hrb : find_minimum_time b k = ok rb), ra.val ≤ rb.val) := by
  sorry

/-- If find_minimum_time(strength,k1) returns r1 and find_minimum_time(strength,k2) returns r2, then r2 <= r1.
  Preconditions: Let strength be a slice with n = len(strength). Assume 1 <= n <= 8 and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. Let k1 and k2 satisfy 1 <= k1 <= k2 <= 10. -/
theorem spec_8 (strength : Slice Std.I64) (k1 k2 : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk210 : k2.val ≤ 10)
    (r1 r2 : Std.I64)
    (hr1 : find_minimum_time strength k1 = ok r1)
    (hr2 : find_minimum_time strength k2 = ok r2) :
    r2.val ≤ r1.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (strength : Slice Std.I64) (k1 k2 : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (hk1 : 1 ≤ k1.val) (hk12 : k1.val ≤ k2.val) (hk210 : k2.val ≤ 10)
    (r1 r2 : Std.I64)
    (hr1 : find_minimum_time strength k1 = ok r1)
    (hr2 : find_minimum_time strength k2 = ok r2), r2.val ≤ r1.val) := by
  sorry

/-- Whenever the function returns a result r, r = min_{0 <= i < n} strength[i] + (n - 1).
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. Assume in addition that strength[i] <= 1 + k for every i with 0 <= i < n. -/
theorem spec_9 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (hsmall : ∀ i : Fin n, strength.val[i.val].val ≤ 1 + k.val) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val = minVal strength.val + ((n : ℤ) - 1) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000)
    (hsmall : ∀ i : Fin n, strength.val[i.val].val ≤ 1 + k.val), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      r.val = minVal strength.val + ((n : ℤ) - 1)) := by
  sorry

/-- The function returns a result r (it does not fail), and 1 <= r <= 8000000; more sharply, r <= sum_{i=0}^{n-1} strength[i].
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_10 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∃ r : Std.I64,
      find_minimum_time strength k = ok r ∧
      1 ≤ r.val ∧ r.val ≤ 8000000 ∧
      r.val ≤ ∑ i : Fin strength.val.length, (strength.val.get i).val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∃ r : Std.I64,
      find_minimum_time strength k = ok r ∧
      1 ≤ r.val ∧ r.val ≤ 8000000 ∧
      r.val ≤ ∑ i : Fin strength.val.length, (strength.val.get i).val) := by
  sorry

/-- Whenever the function returns a result r, there exists a permutation p = (p(0),...,p(n-1)) of the index set {0,...,n-1} such that r = sum_{j=0}^{n-1} ceil(strength[p(j)] / (1 + j*k)) and strength[p(0)] = min_{0 <= i < n} strength[i], where ceil(a/b) for positive integer b and integer a is the least integer t >= 0 with t*b >= a.
  Preconditions: Let n = len(strength). Assume 1 <= n <= 8, 1 <= k <= 10, and for every i with 0 <= i < n, 1 <= strength[i] <= 1000000. -/
theorem spec_11 (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000) :
    ∀ r : Std.I64, find_minimum_time strength k = ok r →
      ∃ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p ∧ r.val = permCost strength.val k.val p ∧
        (strength.val.get (p ⟨0, by omega⟩)).val = minVal strength.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (strength : Slice Std.I64) (k : Std.I64) (n : ℕ)
    (hn : strength.val.length = n)
    (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hk1 : 1 ≤ k.val) (hk10 : k.val ≤ 10)
    (hs : ∀ i : Fin n, 1 ≤ strength.val[i.val].val ∧ strength.val[i.val].val ≤ 1000000), ∀ r : Std.I64, find_minimum_time strength k = ok r →
      ∃ p : Fin strength.val.length → Fin strength.val.length,
        Function.Bijective p ∧ r.val = permCost strength.val k.val p ∧
        (strength.val.get (p ⟨0, by omega⟩)).val = minVal strength.val) := by
  sorry

end AegisSpec.FindMinimumTime
