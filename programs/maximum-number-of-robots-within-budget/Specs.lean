import Aegis.MaximumRobots.Code.Funs

/-!
# Specifications of `Aegis.MaximumRobots.maximum_robots`

LeetCode problem `maximum-number-of-robots-within-budget`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result Aegis.MaximumRobots

namespace AegisSpec.MaximumRobots

def nthVal (l : List I64) (i : ℕ) : ℤ :=
  match l[i]? with
  | some x => x.val
  | none => 0

def sumI (l : List I64) : ℤ := (l.map fun x => x.val).sum

def maxI : List I64 → ℤ
  | [] => 0
  | x :: xs => xs.foldr (fun y acc => max y.val acc) x.val

def revSlice {α : Type} (s : Slice α) : Slice α :=
  Slice.mk s.val.reverse.length (Aeneas.Data.ListN.ListN.fromList s.val.reverse) (by
    rw [List.length_reverse, Slice.val, Aeneas.Data.ListN.ListN_length]
    exact s.bound)

lemma revSlice_val {α : Type} (s : Slice α) : (revSlice s).val = s.val.reverse := by
  simp only [revSlice, Slice.val]
  exact Aeneas.Data.ListN.ListN.from_to_inverse

def cost (cs rs : List I64) (l k : ℕ) : ℤ :=
  if k = 0 then 0
  else maxI ((cs.drop l).take k) + (k : ℤ) * sumI ((rs.drop l).take k)

def HasCostWithin (cs rs : List I64) (n : ℕ) (budget : ℤ) (k : ℤ) : Prop :=
  0 ≤ k ∧ k ≤ (n : ℤ) ∧ ∃ l : ℕ, (l : ℤ) ≤ (n : ℤ) - k ∧ cost cs rs l k.toNat ≤ budget

def IsMaxFeasible (cs rs : List I64) (n : ℕ) (budget : ℤ) (r : ℤ) : Prop :=
  HasCostWithin cs rs n budget r ∧ ∀ k : ℤ, HasCostWithin cs rs n budget k → k ≤ r

def goodRun (cs rs : List I64) (budget : ℤ) (n k : ℕ) : Prop :=
  ∃ l : ℕ, l + k ≤ n ∧ ∀ i : ℕ, l ≤ i → i < l + k → nthVal cs i + nthVal rs i ≤ budget

noncomputable def maxGoodRun (cs rs : List I64) (budget : ℤ) (n : ℕ) : ℕ :=
  letI := Classical.propDecidable
  (Finset.range (n + 1)).sup fun k => if goodRun cs rs budget n k then k else 0

/-- Whenever the function returns a result r, r is the maximum integer k with 0 <= k <= n such that there exists an index l with 0 <= l <= n-k and cost(l, k) <= budget, where cost(l, k) is defined as: cost(l, 0) = 0; and for k >= 1, cost(l, k) = max_{i=l}^{l+k-1} chargeTimes[i] + k * sum_{i=l}^{l+k-1} runningCosts[i].
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_1 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    IsMaxFeasible chargeTimes.val runningCosts.val chargeTimes.val.length budget.val r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), IsMaxFeasible chargeTimes.val runningCosts.val chargeTimes.val.length budget.val r.val) := by
  sorry

/-- The function returns a result r (an i64) and does not fail, panic, or overflow.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_2 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15) :
    ∃ r : I64, maximum_robots chargeTimes runningCosts budget = Result.ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15), ∃ r : I64, maximum_robots chargeTimes runningCosts budget = Result.ok r) := by
  sorry

/-- Whenever the function returns a result r, 0 <= r <= n.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_3 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    0 ≤ r.val ∧ r.val ≤ (chargeTimes.val.length : ℤ) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), 0 ≤ r.val ∧ r.val ≤ (chargeTimes.val.length : ℤ)) := by
  sorry

/-- Whenever the function returns a result r, if r > 0 then there exists an index l with 0 <= l <= n-r such that max_{i=l}^{l+r-1} chargeTimes[i] + r * sum_{i=l}^{l+r-1} runningCosts[i] <= budget.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_4 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    r.val > 0 → ∃ l : ℕ, (l : ℤ) ≤ (chargeTimes.val.length : ℤ) - r.val ∧
      cost chargeTimes.val runningCosts.val l r.val.toNat ≤ budget.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), r.val > 0 → ∃ l : ℕ, (l : ℤ) ≤ (chargeTimes.val.length : ℤ) - r.val ∧
      cost chargeTimes.val runningCosts.val l r.val.toNat ≤ budget.val) := by
  sorry

/-- Whenever the function returns a result r, for every integer k with r < k <= n and every index l with 0 <= l <= n-k, we have max_{i=l}^{l+k-1} chargeTimes[i] + k * sum_{i=l}^{l+k-1} runningCosts[i] > budget.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_5 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    ∀ (k : ℤ), r.val < k → k ≤ (chargeTimes.val.length : ℤ) →
      ∀ l : ℕ, (l : ℤ) ≤ (chargeTimes.val.length : ℤ) - k →
        budget.val < cost chargeTimes.val runningCosts.val l k.toNat := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), ∀ (k : ℤ), r.val < k → k ≤ (chargeTimes.val.length : ℤ) →
      ∀ l : ℕ, (l : ℤ) ≤ (chargeTimes.val.length : ℤ) - k →
        budget.val < cost chargeTimes.val runningCosts.val l k.toNat) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < n, chargeTimes[i] + runningCosts[i] > budget.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_6 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    r.val = 0 ↔ ∀ i : ℕ, i < chargeTimes.val.length →
      budget.val < nthVal chargeTimes.val i + nthVal runningCosts.val i := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), r.val = 0 ↔ ∀ i : ℕ, i < chargeTimes.val.length →
      budget.val < nthVal chargeTimes.val i + nthVal runningCosts.val i) := by
  sorry

/-- Whenever the function returns a result r, r = n if and only if max_{i=0}^{n-1} chargeTimes[i] + n * sum_{i=0}^{n-1} runningCosts[i] <= budget.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_7 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    r.val = (chargeTimes.val.length : ℤ) ↔
      maxI chargeTimes.val + (chargeTimes.val.length : ℤ) * sumI runningCosts.val
        ≤ budget.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), r.val = (chargeTimes.val.length : ℤ) ↔
      maxI chargeTimes.val + (chargeTimes.val.length : ℤ) * sumI runningCosts.val
        ≤ budget.val) := by
  sorry

/-- If the function returns r1 on (chargeTimes, runningCosts, b1) and returns r2 on (chargeTimes, runningCosts, b2), then r1 <= r2.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000. Let b1 and b2 be integers with 1 <= b1 <= b2 <= 10^15. -/
theorem spec_8 (chargeTimes runningCosts : Slice I64) (b1 b2 : I64) (r1 r2 : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hb1 : 1 ≤ b1.val) (hb12 : b1.val ≤ b2.val) (hb2 : b2.val ≤ 10 ^ 15)
    (h1 : maximum_robots chargeTimes runningCosts b1 = Result.ok r1)
    (h2 : maximum_robots chargeTimes runningCosts b2 = Result.ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (b1 b2 : I64) (r1 r2 : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hb1 : 1 ≤ b1.val) (hb12 : b1.val ≤ b2.val) (hb2 : b2.val ≤ 10 ^ 15)
    (h1 : maximum_robots chargeTimes runningCosts b1 = Result.ok r1)
    (h2 : maximum_robots chargeTimes runningCosts b2 = Result.ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If the function returns r1 on (chargeTimes1, runningCosts1, b) and returns r2 on (chargeTimes2, runningCosts2, b), then r1 >= r2.
  Preconditions: Let n be an integer with 1 <= n <= 50000. Let chargeTimes1, runningCosts1, chargeTimes2, runningCosts2 be slices of length n such that for every i with 0 <= i < n, 1 <= chargeTimes1[i] <= 100000, 1 <= runningCosts1[i] <= 100000, 1 <= chargeTimes2[i] <= 100000, and 1 <= runningCosts2[i] <= 100000. Assume for every i with 0 <= i < n, chargeTimes1[i] <= chargeTimes2[i] and runningCosts1[i] <= runningCosts2[i]. Let b be an integer with 1 <= b <= 10^15. -/
theorem spec_9 (chargeTimes1 runningCosts1 chargeTimes2 runningCosts2 : Slice I64)
    (budget : I64)
    (hlen1 : runningCosts1.val.length = chargeTimes1.val.length)
    (hlen2 : chargeTimes2.val.length = chargeTimes1.val.length)
    (hlen3 : runningCosts2.val.length = chargeTimes1.val.length)
    (hn : 1 ≤ chargeTimes1.val.length ∧ chargeTimes1.val.length ≤ 50000)
    (hct1 : ∀ (i : ℕ), i < chargeTimes1.val.length →
      1 ≤ nthVal chargeTimes1.val i ∧ nthVal chargeTimes1.val i ≤ 100000)
    (hrn1 : ∀ (i : ℕ), i < runningCosts1.val.length →
      1 ≤ nthVal runningCosts1.val i ∧ nthVal runningCosts1.val i ≤ 100000)
    (hct2 : ∀ (i : ℕ), i < chargeTimes2.val.length →
      1 ≤ nthVal chargeTimes2.val i ∧ nthVal chargeTimes2.val i ≤ 100000)
    (hrn2 : ∀ (i : ℕ), i < runningCosts2.val.length →
      1 ≤ nthVal runningCosts2.val i ∧ nthVal runningCosts2.val i ≤ 100000)
    (hle_ct : ∀ (i : ℕ), i < chargeTimes1.val.length →
      nthVal chargeTimes1.val i ≤ nthVal chargeTimes2.val i)
    (hle_rn : ∀ (i : ℕ), i < chargeTimes1.val.length →
      nthVal runningCosts1.val i ≤ nthVal runningCosts2.val i)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r1 r2 : I64)
    (h1 : maximum_robots chargeTimes1 runningCosts1 budget = Result.ok r1)
    (h2 : maximum_robots chargeTimes2 runningCosts2 budget = Result.ok r2) :
    r1.val ≥ r2.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (chargeTimes1 runningCosts1 chargeTimes2 runningCosts2 : Slice I64)
    (budget : I64)
    (hlen1 : runningCosts1.val.length = chargeTimes1.val.length)
    (hlen2 : chargeTimes2.val.length = chargeTimes1.val.length)
    (hlen3 : runningCosts2.val.length = chargeTimes1.val.length)
    (hn : 1 ≤ chargeTimes1.val.length ∧ chargeTimes1.val.length ≤ 50000)
    (hct1 : ∀ (i : ℕ), i < chargeTimes1.val.length →
      1 ≤ nthVal chargeTimes1.val i ∧ nthVal chargeTimes1.val i ≤ 100000)
    (hrn1 : ∀ (i : ℕ), i < runningCosts1.val.length →
      1 ≤ nthVal runningCosts1.val i ∧ nthVal runningCosts1.val i ≤ 100000)
    (hct2 : ∀ (i : ℕ), i < chargeTimes2.val.length →
      1 ≤ nthVal chargeTimes2.val i ∧ nthVal chargeTimes2.val i ≤ 100000)
    (hrn2 : ∀ (i : ℕ), i < runningCosts2.val.length →
      1 ≤ nthVal runningCosts2.val i ∧ nthVal runningCosts2.val i ≤ 100000)
    (hle_ct : ∀ (i : ℕ), i < chargeTimes1.val.length →
      nthVal chargeTimes1.val i ≤ nthVal chargeTimes2.val i)
    (hle_rn : ∀ (i : ℕ), i < chargeTimes1.val.length →
      nthVal runningCosts1.val i ≤ nthVal runningCosts2.val i)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r1 r2 : I64)
    (h1 : maximum_robots chargeTimes1 runningCosts1 budget = Result.ok r1)
    (h2 : maximum_robots chargeTimes2 runningCosts2 budget = Result.ok r2), r1.val ≥ r2.val) := by
  sorry

/-- If the function returns r on (chargeTimes, runningCosts, budget) and returns r' on (revCharge, revRunning, budget), then r = r'.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. Define revCharge and revRunning of length n by revCharge[i] = chargeTimes[n-1-i] and revRunning[i] = runningCosts[n-1-i] for 0 <= i < n. -/
theorem spec_10 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r r' : I64)
    (h1 : maximum_robots chargeTimes runningCosts budget = Result.ok r)
    (h2 : maximum_robots (revSlice chargeTimes) (revSlice runningCosts) budget
      = Result.ok r') :
    r = r' := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r r' : I64)
    (h1 : maximum_robots chargeTimes runningCosts budget = Result.ok r)
    (h2 : maximum_robots (revSlice chargeTimes) (revSlice runningCosts) budget
      = Result.ok r'), r = r') := by
  sorry

/-- Whenever the function returns a result r, let good(i) be the predicate chargeTimes[i] + runningCosts[i] <= budget for 0 <= i < n. Let maxGoodRun be the maximum integer k with 0 <= k <= n such that there exists an index l with 0 <= l <= n-k and for every i with l <= i < l+k, good(i) holds. Then r <= maxGoodRun.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n <= 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. -/
theorem spec_11 (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r) :
    r.val ≤ (maxGoodRun chargeTimes.val runningCosts.val budget.val
      chargeTimes.val.length : ℤ) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (chargeTimes runningCosts : Slice I64) (budget : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length ≤ 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (r : I64) (hres : maximum_robots chargeTimes runningCosts budget = Result.ok r), r.val ≤ (maxGoodRun chargeTimes.val runningCosts.val budget.val
      chargeTimes.val.length : ℤ)) := by
  sorry

/-- If the function returns r on (chargeTimes, runningCosts, budget) and returns r' on (chargeTimes', runningCosts', budget), then r' >= r.
  Preconditions: Let n = len(chargeTimes) = len(runningCosts). Assume 1 <= n < 50000, for every i with 0 <= i < n, 1 <= chargeTimes[i] <= 100000 and 1 <= runningCosts[i] <= 100000, and 1 <= budget <= 10^15. Let c and rc be integers with 1 <= c <= 100000 and 1 <= rc <= 100000. Define chargeTimes' of length n+1 by chargeTimes'[i] = chargeTimes[i] for 0 <= i < n and chargeTimes'[n] = c. Define runningCosts' of length n+1 by runningCosts'[i] = runningCosts[i] for 0 <= i < n and runningCosts'[n] = rc. -/
theorem spec_12 (chargeTimes runningCosts chargeTimes' runningCosts' : Slice I64)
    (budget c rc : I64) (r r' : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length < 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (hc : 1 ≤ c.val ∧ c.val ≤ 100000)
    (hrc : 1 ≤ rc.val ∧ rc.val ≤ 100000)
    (hchargeTimes' : chargeTimes'.val = chargeTimes.val ++ [c])
    (hrunningCosts' : runningCosts'.val = runningCosts.val ++ [rc])
    (h1 : maximum_robots chargeTimes runningCosts budget = Result.ok r)
    (h2 : maximum_robots chargeTimes' runningCosts' budget = Result.ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (chargeTimes runningCosts chargeTimes' runningCosts' : Slice I64)
    (budget c rc : I64) (r r' : I64)
    (hlen : chargeTimes.val.length = runningCosts.val.length)
    (hn : 1 ≤ chargeTimes.val.length ∧ chargeTimes.val.length < 50000)
    (hct : ∀ (i : ℕ), i < chargeTimes.val.length →
      1 ≤ nthVal chargeTimes.val i ∧ nthVal chargeTimes.val i ≤ 100000)
    (hrn : ∀ (i : ℕ), i < runningCosts.val.length →
      1 ≤ nthVal runningCosts.val i ∧ nthVal runningCosts.val i ≤ 100000)
    (hbudget : 1 ≤ budget.val ∧ budget.val ≤ 10 ^ 15)
    (hc : 1 ≤ c.val ∧ c.val ≤ 100000)
    (hrc : 1 ≤ rc.val ∧ rc.val ≤ 100000)
    (hchargeTimes' : chargeTimes'.val = chargeTimes.val ++ [c])
    (hrunningCosts' : runningCosts'.val = runningCosts.val ++ [rc])
    (h1 : maximum_robots chargeTimes runningCosts budget = Result.ok r)
    (h2 : maximum_robots chargeTimes' runningCosts' budget = Result.ok r'), r.val ≤ r'.val) := by
  sorry

end AegisSpec.MaximumRobots
