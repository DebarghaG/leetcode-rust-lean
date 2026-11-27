import Aegis.MaximumProfit.Code.Funs

/-!
# Specifications of `Aegis.MaximumProfit.maximum_profit`

LeetCode problem `maximum-profit-from-trading-stocks`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MaximumProfit

  def entry (s : Slice I64) (i : Nat) : Int := (s.val.getD i 0#i64).val

  def indices (n : Nat) : Finset Nat := Finset.range n

  def cost (present : Slice I64) (S : Finset Nat) : Int :=
    S.sum (fun i => entry present i)

  def profit (present future : Slice I64) (S : Finset Nat) : Int :=
    S.sum (fun i => entry future i - entry present i)

  def affordable (present : Slice I64) (n : Nat) (budget : Int) : Finset Nat :=
    (indices n).filter (fun i => entry present i ≤ budget)

  def feasibleSubsets (present : Slice I64) (s : Finset Nat) (budget : Int) :
      Finset (Finset Nat) :=
    s.powerset.filter (fun S => cost present S ≤ budget)

  def maxZero (s : Finset Int) : Int :=
    (insert 0 s).max' (Finset.insert_nonempty 0 s)

  def bestProfit (present future : Slice I64) (s : Finset Nat) (budget : Int) : Int :=
    maxZero ((feasibleSubsets present s budget).image (fun S => profit present future S))

  def bestSingle (present future : Slice I64) (n : Nat) (budget : Int) : Int :=
    maxZero ((affordable present n budget).image (fun i => entry future i - entry present i))

  def totalGain (present future : Slice I64) (n : Nat) : Int :=
    (indices n).sum (fun i => max 0 (entry future i - entry present i))

  def zeroCostGain (present future : Slice I64) (n : Nat) : Int :=
    (indices n).sum
      (fun i => if entry present i = 0 then max 0 (entry future i - entry present i) else 0)

  /-- The function returns a result r (i.e., it does not fail) and r = max( {0} ∪ { sum_{i in S} (future[i] - present[i]) | S ⊆ {0, ..., n-1} and sum_{i in S} present[i] <= budget } ).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_1 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        r.val = bestProfit present future (indices n) budget.val := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          r.val = bestProfit present future (indices n) budget.val) := by
    sorry

  /-- The function returns a result r and 0 <= r <= sum_{i=0}^{n-1} max(0, future[i] - present[i]).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_2 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        0 ≤ r.val ∧ r.val ≤ totalGain present future n := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          0 ≤ r.val ∧ r.val ≤ totalGain present future n) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail) and r >= max({0} union { future[i] - present[i] | 0 <= i < n and present[i] <= budget }).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_3 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        bestSingle present future n budget.val ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          bestSingle present future n budget.val ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{n-1} (if present[i] = 0 then max(0, future[i] - present[i]) else 0).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000; budget = 0. -/
  theorem spec_4 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
      (h_zero : budget.val = 0) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        r.val = zeroCostGain present future n := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
        (h_zero : budget.val = 0), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          r.val = zeroCostGain present future n) := by
    sorry

  /-- The function returns a result r and r = sum_{i=0}^{n-1} max(0, future[i] - present[i]).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000; budget >= sum_{i=0}^{n-1} present[i]. -/
  theorem spec_5 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
      (h_big : cost present (indices n) ≤ budget.val) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        r.val = totalGain present future n := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
        (h_big : cost present (indices n) ≤ budget.val), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          r.val = totalGain present future n) := by
    sorry

  /-- The function returns a result r and there exists a subset S ⊆ {0, ..., n-1} such that sum_{i in S} present[i] <= budget and r = sum_{i in S} (future[i] - present[i]).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_6 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        ∃ S : Finset Nat, S ⊆ indices n ∧ cost present S ≤ budget.val ∧
          r.val = profit present future S := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          ∃ S : Finset Nat, S ⊆ indices n ∧ cost present S ≤ budget.val ∧
            r.val = profit present future S) := by
    sorry

  /-- The function returns a result r and for every subset S ⊆ {0, ..., n-1} with sum_{i in S} present[i] <= budget, we have sum_{i in S} (future[i] - present[i]) <= r.
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_7 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        ∀ S : Finset Nat, S ⊆ indices n → cost present S ≤ budget.val →
          profit present future S ≤ r.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          ∀ S : Finset Nat, S ⊆ indices n → cost present S ≤ budget.val →
            profit present future S ≤ r.val) := by
    sorry

  /-- The function returns a result r and r = max( {0} ∪ { sum_{i in S} (future[i] - present[i]) | S ⊆ { i | 0 <= i < n and present[i] <= budget } and sum_{i in S} present[i] <= budget } ).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_8 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        r.val = bestProfit present future (affordable present n budget.val) budget.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          r.val = bestProfit present future (affordable present n budget.val) budget.val) := by
    sorry

  /-- The function returns a result r (i.e., it does not fail; the result is Ok r).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_9 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r) := by
    sorry

  /-- The function returns a result r and r = 0 if and only if for every subset S ⊆ {0, ..., n-1} with sum_{i in S} present[i] <= budget, we have sum_{i in S} (future[i] - present[i]) <= 0.
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_10 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        (r.val = 0 ↔ ∀ S : Finset Nat, S ⊆ indices n → cost present S ≤ budget.val →
          profit present future S ≤ 0) := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          (r.val = 0 ↔ ∀ S : Finset Nat, S ⊆ indices n → cost present S ≤ budget.val →
            profit present future S ≤ 0)) := by
    sorry

  /-- The function returns a result r and for that unique index i, r = max(0, future[i] - present[i]).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000; there exists exactly one index i with 0 <= i < n such that present[i] <= budget. -/
  theorem spec_11 (present future : Slice I64) (budget : I64) (n i : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ j, j < n → 0 ≤ entry present j ∧ entry present j ≤ 100)
      (h_future : ∀ j, j < n → 0 ≤ entry future j ∧ entry future j ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
      (hi_lt : i < n) (hi_affordable : entry present i ≤ budget.val)
      (h_unique : ∀ j, j < n → entry present j ≤ budget.val → j = i) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        r.val = max 0 (entry future i - entry present i) := by
    sorry

  theorem spec_11_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n i : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ j, j < n → 0 ≤ entry present j ∧ entry present j ≤ 100)
        (h_future : ∀ j, j < n → 0 ≤ entry future j ∧ entry future j ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000)
        (hi_lt : i < n) (hi_affordable : entry present i ≤ budget.val)
        (h_unique : ∀ j, j < n → entry present j ≤ budget.val → j = i), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          r.val = max 0 (entry future i - entry present i)) := by
    sorry

  /-- Both calls maximum_profit(present, future, budget1) and maximum_profit(present, future, budget2) return results, and if their returned values are r1 and r2 respectively, then r1 <= r2.
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget1 <= budget2 <= 1000. -/
  theorem spec_12 (present future : Slice I64) (budget1 budget2 : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget1 : 0 ≤ budget1.val ∧ budget1.val ≤ 1000)
      (h_budget2 : 0 ≤ budget2.val ∧ budget2.val ≤ 1000)
      (h_le : budget1.val ≤ budget2.val) :
      ∃ r1 r2, Aegis.MaximumProfit.maximum_profit present future budget1 = ok r1 ∧
        Aegis.MaximumProfit.maximum_profit present future budget2 = ok r2 ∧
        r1.val ≤ r2.val := by
    sorry

  theorem spec_12_neg :
      ¬ (∀ (present future : Slice I64) (budget1 budget2 : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget1 : 0 ≤ budget1.val ∧ budget1.val ≤ 1000)
        (h_budget2 : 0 ≤ budget2.val ∧ budget2.val ≤ 1000)
        (h_le : budget1.val ≤ budget2.val), ∃ r1 r2, Aegis.MaximumProfit.maximum_profit present future budget1 = ok r1 ∧
          Aegis.MaximumProfit.maximum_profit present future budget2 = ok r2 ∧
          r1.val ≤ r2.val) := by
    sorry

  /-- The function returns a result r and there exists a subset S of {0, ..., n-1} such that sum_{i in S} present[i] <= budget, r = sum_{i in S} (future[i] - present[i]), and for every i in S, future[i] > present[i].
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_13 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        ∃ S : Finset Nat, S ⊆ indices n ∧ cost present S ≤ budget.val ∧
          r.val = profit present future S ∧ ∀ i ∈ S, entry present i < entry future i := by
    sorry

  theorem spec_13_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          ∃ S : Finset Nat, S ⊆ indices n ∧ cost present S ≤ budget.val ∧
            r.val = profit present future S ∧ ∀ i ∈ S, entry present i < entry future i) := by
    sorry

  /-- The function returns a result r and r >= sum_{i=0}^{n-1} (if present[i] = 0 then max(0, future[i] - present[i]) else 0).
    Preconditions: n = len(present) = len(future); 1 <= n <= 1000; for every i with 0 <= i < n, 0 <= present[i] <= 100 and 0 <= future[i] <= 100; 0 <= budget <= 1000. -/
  theorem spec_14 (present future : Slice I64) (budget : I64) (n : Nat)
      (hn_present : present.val.length = n) (hn_future : future.val.length = n)
      (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
      (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
      (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
      (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000) :
      ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
        zeroCostGain present future n ≤ r.val := by
    sorry

  theorem spec_14_neg :
      ¬ (∀ (present future : Slice I64) (budget : I64) (n : Nat)
        (hn_present : present.val.length = n) (hn_future : future.val.length = n)
        (hn_lo : 1 ≤ n) (hn_hi : n ≤ 1000)
        (h_present : ∀ i, i < n → 0 ≤ entry present i ∧ entry present i ≤ 100)
        (h_future : ∀ i, i < n → 0 ≤ entry future i ∧ entry future i ≤ 100)
        (h_budget : 0 ≤ budget.val ∧ budget.val ≤ 1000), ∃ r, Aegis.MaximumProfit.maximum_profit present future budget = ok r ∧
          zeroCostGain present future n ≤ r.val) := by
    sorry

  end AegisSpec.MaximumProfit
