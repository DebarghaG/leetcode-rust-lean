import Aegis.MaxCount.Code.Funs

/-!
# Specifications of `Aegis.MaxCount.max_count`

LeetCode problem `maximum-number-of-integers-to-choose-from-a-range-i`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxCount

namespace AegisSpec.MaxCount

def sliceVals (s : Slice I64) : List ℤ := s.val.map (fun x => x.val)

def bannedSet (banned : Slice I64) : Finset ℤ := (sliceVals banned).toFinset

def upToSet (n : ℤ) : Finset ℤ :=
  ((List.range n.toNat).map (fun k => (k : ℤ) + 1)).toFinset

def allowedSet (banned : Slice I64) (n : ℤ) : Finset ℤ :=
  upToSet n \ bannedSet banned

def Feasible (banned : Slice I64) (n maxSum : ℤ) (S : Finset ℤ) : Prop :=
  S ⊆ allowedSet banned n ∧ S.sum (fun x => x) ≤ maxSum

def IsMaxCard (banned : Slice I64) (n maxSum r : ℤ) : Prop :=
  (∃ S : Finset ℤ, Feasible banned n maxSum S ∧ (S.card : ℤ) = r) ∧
    ∀ T : Finset ℤ, Feasible banned n maxSum T → (T.card : ℤ) ≤ r

def IsAllowedEnum (banned : Slice I64) (n : ℤ) (a : List ℤ) : Prop :=
  a.Pairwise (· < ·) ∧ (∀ x ∈ a, x ∈ allowedSet banned n) ∧
    (∀ x : ℤ, x ∈ allowedSet banned n → x ∈ a)

def prefixSum (a : List ℤ) (k : ℕ) : ℤ := (a.take k).sum

/-- The function returns a result r (it does not fail), and r is the maximum cardinality of a finite set S of integers such that: every x in S satisfies 1 <= x <= n; for every x in S and every i with 0 <= i < len(banned), x != banned[i]; and sum_{x in S} x <= maxSum. Equivalently, there exists such a set S with |S| = r, and every such set T satisfies |T| <= r.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_1 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000) :
    ∃ r : I64, max_count banned n maxSum = ok r ∧
      IsMaxCard banned n.val maxSum.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000), ∃ r : I64, max_count banned n maxSum = ok r ∧
      IsMaxCard banned n.val maxSum.val r.val) := by
  sorry

/-- The function returns a result r (it does not fail) for the given banned, n, and maxSum.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_2 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000) :
    ∃ r : I64, max_count banned n maxSum = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000), ∃ r : I64, max_count banned n maxSum = ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_3 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    0 ≤ r.val ∧ r.val ≤ n.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r), 0 ≤ r.val ∧ r.val ≤ n.val) := by
  sorry

/-- Whenever the function returns a result r, r*(r+1)/2 <= maxSum.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_4 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    r.val * (r.val + 1) / 2 ≤ maxSum.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r), r.val * (r.val + 1) / 2 ≤ maxSum.val) := by
  sorry

/-- Whenever the function returns a result r, if there is no integer x such that 1 <= x <= n, x != banned[i] for every i with 0 <= i < len(banned), and x <= maxSum, then r = 0.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_5 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r)
    (hempty : ∀ x : ℤ, ¬ (1 ≤ x ∧ x ≤ n.val ∧ x ∉ bannedSet banned ∧
      x ≤ maxSum.val)) :
    r.val = 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r)
    (hempty : ∀ x : ℤ, ¬ (1 ≤ x ∧ x ≤ n.val ∧ x ∉ bannedSet banned ∧
      x ≤ maxSum.val)), r.val = 0) := by
  sorry

/-- Let A be the set of integers x such that 1 <= x <= n and x != banned[i] for every i with 0 <= i < len(banned). Whenever the function returns a result r, if sum_{x in A} x <= maxSum, then r = |A|.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_6 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r)
    (hsum : (allowedSet banned n.val).sum (fun x => x) ≤ maxSum.val) :
    r.val = ((allowedSet banned n.val).card : ℤ) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r)
    (hsum : (allowedSet banned n.val).sum (fun x => x) ≤ maxSum.val), r.val = ((allowedSet banned n.val).card : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if for every i with 0 <= i < len(banned), banned[i] < 1 or banned[i] > n, then r is the largest integer k such that 0 <= k <= n and k*(k+1)/2 <= maxSum.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_7 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hout : ∀ x ∈ sliceVals banned, x < 1 ∨ x > n.val)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    IsGreatest {k : ℤ | 0 ≤ k ∧ k ≤ n.val ∧ k * (k + 1) / 2 ≤ maxSum.val}
      r.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hout : ∀ x ∈ sliceVals banned, x < 1 ∨ x > n.val)
    (r : I64) (hr : max_count banned n maxSum = ok r), IsGreatest {k : ℤ | 0 ≤ k ∧ k ≤ n.val ∧ k * (k + 1) / 2 ≤ maxSum.val}
      r.val) := by
  sorry

/-- Let a_1 < a_2 < ... < a_m be all integers x such that 1 <= x <= n and x != banned[i] for every i with 0 <= i < len(banned). Whenever the function returns a result r, 0 <= r <= m and, if r > 0, sum_{j=1}^{r} a_j <= maxSum.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_8 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (a : List ℤ) (ha : IsAllowedEnum banned n.val a)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    0 ≤ r.val ∧ r.val ≤ (a.length : ℤ) ∧
      (0 < r.val → prefixSum a r.val.toNat ≤ maxSum.val) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (a : List ℤ) (ha : IsAllowedEnum banned n.val a)
    (r : I64) (hr : max_count banned n maxSum = ok r), 0 ≤ r.val ∧ r.val ≤ (a.length : ℤ) ∧
      (0 < r.val → prefixSum a r.val.toNat ≤ maxSum.val)) := by
  sorry

/-- Whenever the function returns a result r, for every finite set T of integers such that every x in T satisfies 1 <= x <= n and x != banned[i] for every i with 0 <= i < len(banned), and sum_{x in T} x <= maxSum, we have |T| <= r.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_9 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    ∀ T : Finset ℤ, Feasible banned n.val maxSum.val T → (T.card : ℤ) ≤ r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (r : I64) (hr : max_count banned n maxSum = ok r), ∀ T : Finset ℤ, Feasible banned n.val maxSum.val T → (T.card : ℤ) ≤ r.val) := by
  sorry

/-- Let a_1 < a_2 < ... < a_m be all integers x such that 1 <= x <= n and x != banned[i] for every i with 0 <= i < len(banned). Whenever the function returns a result r, if r < m then sum_{j=1}^{r+1} a_j > maxSum.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_10 (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (a : List ℤ) (ha : IsAllowedEnum banned n.val a)
    (r : I64) (hr : max_count banned n maxSum = ok r) :
    r.val < (a.length : ℤ) → 0 ≤ r.val →
      prefixSum a (r.val.toNat + 1) > maxSum.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (a : List ℤ) (ha : IsAllowedEnum banned n.val a)
    (r : I64) (hr : max_count banned n maxSum = ok r), r.val < (a.length : ℤ) → 0 ≤ r.val →
      prefixSum a (r.val.toNat + 1) > maxSum.val) := by
  sorry

/-- For every integer maxSum2 with maxSum <= maxSum2 <= 1000000000, if the function returns r on inputs (banned, n, maxSum) and returns r2 on inputs (banned, n, maxSum2), then r <= r2.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_11 (banned : Slice I64) (n maxSum maxSum2 : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hm2a : maxSum.val ≤ maxSum2.val) (hm2b : maxSum2.val ≤ 1000000000)
    (r r2 : I64) (hr : max_count banned n maxSum = ok r)
    (hr2 : max_count banned n maxSum2 = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (banned : Slice I64) (n maxSum maxSum2 : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hm2a : maxSum.val ≤ maxSum2.val) (hm2b : maxSum2.val ≤ 1000000000)
    (r r2 : I64) (hr : max_count banned n maxSum = ok r)
    (hr2 : max_count banned n maxSum2 = ok r2), r.val ≤ r2.val) := by
  sorry

/-- For every integer n2 with n <= n2 <= 10000, if the function returns r on inputs (banned, n, maxSum) and returns r2 on inputs (banned, n2, maxSum), then r <= r2.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000. -/
theorem spec_12 (banned : Slice I64) (n n2 maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hn2a : n.val ≤ n2.val) (hn2b : n2.val ≤ 10000)
    (r r2 : I64) (hr : max_count banned n maxSum = ok r)
    (hr2 : max_count banned n2 maxSum = ok r2) :
    r.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (banned : Slice I64) (n n2 maxSum : I64)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hn2a : n.val ≤ n2.val) (hn2b : n2.val ≤ 10000)
    (r r2 : I64) (hr : max_count banned n maxSum = ok r)
    (hr2 : max_count banned n2 maxSum = ok r2), r.val ≤ r2.val) := by
  sorry

/-- Suppose for every integer x with 1 <= x <= n, there exists i with 0 <= i < len(b1) and b1[i] = x if and only if there exists j with 0 <= j < len(b2) and b2[j] = x. If the function returns r1 on inputs (b1, n, maxSum) and returns r2 on inputs (b2, n, maxSum), then r1 = r2.
  Preconditions: 1 <= n <= 10000; 1 <= maxSum <= 1000000000; for both slices b1 and b2, 0 <= len(b1), len(b2) <= 10000 and every entry is between 1 and 10000. -/
theorem spec_13 (b1 b2 : Slice I64) (n maxSum : I64)
    (hb1len : b1.val.length ≤ 10000) (hb2len : b2.val.length ≤ 10000)
    (hb1val : ∀ x ∈ sliceVals b1, 1 ≤ x ∧ x ≤ 10000)
    (hb2val : ∀ x ∈ sliceVals b2, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hsame : ∀ x : ℤ, 1 ≤ x → x ≤ n.val → (x ∈ sliceVals b1 ↔ x ∈ sliceVals b2))
    (r1 r2 : I64) (hr1 : max_count b1 n maxSum = ok r1)
    (hr2 : max_count b2 n maxSum = ok r2) :
    r1.val = r2.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (b1 b2 : Slice I64) (n maxSum : I64)
    (hb1len : b1.val.length ≤ 10000) (hb2len : b2.val.length ≤ 10000)
    (hb1val : ∀ x ∈ sliceVals b1, 1 ≤ x ∧ x ≤ 10000)
    (hb2val : ∀ x ∈ sliceVals b2, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hsame : ∀ x : ℤ, 1 ≤ x → x ≤ n.val → (x ∈ sliceVals b1 ↔ x ∈ sliceVals b2))
    (r1 r2 : I64) (hr1 : max_count b1 n maxSum = ok r1)
    (hr2 : max_count b2 n maxSum = ok r2), r1.val = r2.val) := by
  sorry

/-- Let banned' be the slice of length len(banned)-1 such that banned'[k] = banned[k] for 0 <= k < j and banned'[k] = banned[k+1] for j <= k < len(banned)-1. If the function returns r on inputs (banned, n, maxSum) and returns r' on inputs (banned', n, maxSum), then r = r'.
  Preconditions: 0 <= len(banned) <= 10000; for every i with 0 <= i < len(banned), 1 <= banned[i] <= 10000; 1 <= n <= 10000; 1 <= maxSum <= 1000000000; j is an index with 0 <= j < len(banned) and banned[j] > maxSum. -/
theorem spec_14 (banned banned' : Slice I64) (n maxSum : I64) (j : ℕ)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hj : j < banned.val.length)
    (hbanned' : sliceVals banned' = (sliceVals banned).eraseIdx j)
    (hbj : maxSum.val < (banned.val[j]).val)
    (r r' : I64) (hr : max_count banned n maxSum = ok r)
    (hr' : max_count banned' n maxSum = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (banned banned' : Slice I64) (n maxSum : I64) (j : ℕ)
    (hblen : banned.val.length ≤ 10000)
    (hbval : ∀ x ∈ sliceVals banned, 1 ≤ x ∧ x ≤ 10000)
    (hn1 : 1 ≤ n.val) (hn2 : n.val ≤ 10000)
    (hm1 : 1 ≤ maxSum.val) (hm2 : maxSum.val ≤ 1000000000)
    (hj : j < banned.val.length)
    (hbanned' : sliceVals banned' = (sliceVals banned).eraseIdx j)
    (hbj : maxSum.val < (banned.val[j]).val)
    (r r' : I64) (hr : max_count banned n maxSum = ok r)
    (hr' : max_count banned' n maxSum = ok r'), r.val = r'.val) := by
  sorry

def sampleBanned : Slice I64 :=
  Slice.mk 2 (.cons 2#i64 (.cons 5#i64 .nil)) (by scalar_tac)

end AegisSpec.MaxCount
