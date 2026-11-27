import Aegis.MaxProfitAssignment.Code.Funs

/-!
# Specifications of `Aegis.MaxProfitAssignment.max_profit_assignment`

LeetCode problem `most-profit-assigning-work`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxProfitAssignment

namespace AegisSpec.MaxProfitAssignment

def valAt (s : Slice I64) (i : Nat) : Int := (s.val.getD i 0#i64).val

def maxOfList (l : List Int) : Int := l.max?.getD 0

def bestProfit (difficulty profit : Slice I64) (w : Int) : Int :=
  maxOfList ((difficulty.val.zip profit.val).filterMap (fun dp =>
    if dp.1.val ≤ w then some dp.2.val else none))

def totalBestProfit (difficulty profit worker : Slice I64) : Int :=
  (worker.val.map (fun w => bestProfit difficulty profit w.val)).sum

def maxProfit (profit : Slice I64) : Int := maxOfList (profit.val.map (fun x => x.val))

def countAffordable (difficulty worker : Slice I64) : Nat :=
  (worker.val.filter (fun w =>
    (List.range difficulty.val.length).any (fun i => decide (valAt difficulty i ≤ w.val)))).length

def countAtLeast (worker : Slice I64) (d : Int) : Nat :=
  (worker.val.filter (fun w => decide (d ≤ w.val))).length

def pairsOf (difficulty profit : Slice I64) : List (Int × Int) :=
  (difficulty.val.zip profit.val).map (fun dp => (dp.1.val, dp.2.val))

def FeasibleAssignment (difficulty worker : Slice I64) (a : Nat → Option Nat) : Prop :=
  ∀ j, j < worker.val.length → ∀ i, a j = some i →
    i < difficulty.val.length ∧ valAt difficulty i ≤ valAt worker j

def UsesJobWhenPossible (difficulty worker : Slice I64) (a : Nat → Option Nat) : Prop :=
  ∀ j, j < worker.val.length → a j = none →
    ∀ i, i < difficulty.val.length → ¬ valAt difficulty i ≤ valAt worker j

def assignmentProfit (profit : Slice I64) (m : Nat) (a : Nat → Option Nat) : Int :=
  ((List.range m).map (fun j => match a j with
    | some i => valAt profit i
    | none => 0)).sum

/-- Let bestProfit(w) be defined as follows: if there is at least one i with 0 <= i < len(difficulty) and difficulty[i] <= w, then bestProfit(w) = max{ profit[i] | 0 <= i < len(difficulty) and difficulty[i] <= w }; otherwise bestProfit(w) = 0. The function returns a result r and r = sum_{j=0}^{len(worker)-1} bestProfit(worker[j]).
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_1 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r : I64, max_profit_assignment difficulty profit worker = ok r ∧
      r.val = totalBestProfit difficulty profit worker := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r : I64, max_profit_assignment difficulty profit worker = ok r ∧
      r.val = totalBestProfit difficulty profit worker) := by
  sorry

/-- For every input satisfying the preconditions, the function returns a result r and does not fail: it does not panic, access out of bounds, or overflow i64 arithmetic.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_2 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000) :
    ∃ r : I64, max_profit_assignment difficulty profit worker = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000), ∃ r : I64, max_profit_assignment difficulty profit worker = ok r) := by
  sorry

/-- Whenever the function returns a result r, r >= 0.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_3 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), 0 ≤ r.val) := by
  sorry

/-- Let M = max{ profit[i] | 0 <= i < len(difficulty) }. Whenever the function returns a result r, r <= len(worker) * M.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_4 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    r.val ≤ (worker.val.length : Int) * maxProfit profit := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), r.val ≤ (worker.val.length : Int) * maxProfit profit) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every j with 0 <= j < len(worker) and every i with 0 <= i < len(difficulty), difficulty[i] > worker[j].
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_5 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    (r.val = 0 ↔ ∀ (j : Nat), j < worker.val.length →
      ∀ (i : Nat), i < difficulty.val.length → valAt worker j < valAt difficulty i) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), (r.val = 0 ↔ ∀ (j : Nat), j < worker.val.length →
      ∀ (i : Nat), i < difficulty.val.length → valAt worker j < valAt difficulty i)) := by
  sorry

/-- Let bestProfit(w) be the maximum profit[i] over all i with 0 <= i < len(difficulty) and difficulty[i] <= w, or 0 if no such i exists. Whenever the function returns a result r, r = len(worker) * bestProfit(w).
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; and there exists an integer w such that worker[j] = w for every 0 <= j < len(worker). -/
theorem spec_6 (difficulty profit worker : Slice I64) (w : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hw : ∀ x ∈ worker.val, x.val = w)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    r.val = (worker.val.length : Int) * bestProfit difficulty profit w := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (difficulty profit worker : Slice I64) (w : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hw : ∀ x ∈ worker.val, x.val = w)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), r.val = (worker.val.length : Int) * bestProfit difficulty profit w) := by
  sorry

/-- If the function returns r on (difficulty, profit, worker), r1 on (difficulty, profit, w1), and r2 on (difficulty, profit, w2), then r = r1 + r2.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(worker) >= 2; w1 and w2 are nonempty slices; len(w1) + len(w2) = len(worker); worker is the concatenation of w1 and w2, meaning worker[j] = w1[j] for 0 <= j < len(w1) and worker[len(w1) + j] = w2[j] for 0 <= j < len(w2); and every element of w1 and w2 is between 1 and 100000. -/
theorem spec_7 (difficulty profit worker w1 w2 : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm_ge : 2 ≤ worker.val.length)
    (hcat : worker.val = w1.val ++ w2.val)
    (h1_ne : 1 ≤ w1.val.length) (h2_ne : 1 ≤ w2.val.length)
    (h1_bounds : ∀ x ∈ w1.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h2_bounds : ∀ x ∈ w2.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r r1 r2 : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr1 : max_profit_assignment difficulty profit w1 = ok r1)
    (hr2 : max_profit_assignment difficulty profit w2 = ok r2) :
    r.val = r1.val + r2.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (difficulty profit worker w1 w2 : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm_ge : 2 ≤ worker.val.length)
    (hcat : worker.val = w1.val ++ w2.val)
    (h1_ne : 1 ≤ w1.val.length) (h2_ne : 1 ≤ w2.val.length)
    (h1_bounds : ∀ x ∈ w1.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (h2_bounds : ∀ x ∈ w2.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r r1 r2 : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr1 : max_profit_assignment difficulty profit w1 = ok r1)
    (hr2 : max_profit_assignment difficulty profit w2 = ok r2), r.val = r1.val + r2.val) := by
  sorry

/-- If the function returns r on (difficulty, profit, worker) and r' on (difficulty, profit, worker'), then r = r'.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(worker') = len(worker); worker' is a permutation of worker; and every element of worker' is between 1 and 100000. -/
theorem spec_8 (difficulty profit worker worker' : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm'_len : worker'.val.length = worker.val.length)
    (hperm : worker'.val.Perm worker.val)
    (hwork' : ∀ x ∈ worker'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit worker' = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (difficulty profit worker worker' : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm'_len : worker'.val.length = worker.val.length)
    (hperm : worker'.val.Perm worker.val)
    (hwork' : ∀ x ∈ worker'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit worker' = ok r'), r.val = r'.val) := by
  sorry

/-- If the function returns r on (difficulty, profit, worker) and r' on (difficulty', profit', worker), then r = r'.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(difficulty') = len(profit'); 1 <= len(difficulty') <= 10000; for every i with 0 <= i < len(difficulty'), 1 <= difficulty'[i] <= 100000 and 1 <= profit'[i] <= 100000; len(difficulty') = len(difficulty); len(profit') = len(profit); and there exists a permutation pi of {0, ..., len(difficulty)-1} such that difficulty'[i] = difficulty[pi(i)] and profit'[i] = profit[pi(i)] for every 0 <= i < len(difficulty). -/
theorem spec_9 (difficulty profit difficulty' profit' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd'_len : difficulty'.val.length = profit'.val.length)
    (hd'_lo : 1 ≤ difficulty'.val.length) (hd'_hi : difficulty'.val.length ≤ 10000)
    (hd'_bounds : ∀ x ∈ difficulty'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp'_bounds : ∀ x ∈ profit'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd_same_len : difficulty'.val.length = difficulty.val.length)
    (hp_same_len : profit'.val.length = profit.val.length)
    (hperm : (pairsOf difficulty' profit').Perm (pairsOf difficulty profit))
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty' profit' worker = ok r') :
    r.val = r'.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (difficulty profit difficulty' profit' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd'_len : difficulty'.val.length = profit'.val.length)
    (hd'_lo : 1 ≤ difficulty'.val.length) (hd'_hi : difficulty'.val.length ≤ 10000)
    (hd'_bounds : ∀ x ∈ difficulty'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp'_bounds : ∀ x ∈ profit'.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd_same_len : difficulty'.val.length = difficulty.val.length)
    (hp_same_len : profit'.val.length = profit.val.length)
    (hperm : (pairsOf difficulty' profit').Perm (pairsOf difficulty profit))
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty' profit' worker = ok r'), r.val = r'.val) := by
  sorry

/-- If the function returns r on (difficulty, profit, worker) and r' on (difficulty, profit, worker'), then r <= r'.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(worker') = len(worker); and for every j with 0 <= j < len(worker), 1 <= worker[j] <= worker'[j] <= 100000. -/
theorem spec_10 (difficulty profit worker worker' : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm'_len : worker'.val.length = worker.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) worker.val worker'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit worker' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (difficulty profit worker worker' : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hm'_len : worker'.val.length = worker.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) worker.val worker'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit worker' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- If the function returns r on (difficulty, profit, worker) and r' on (difficulty, profit', worker), then r <= r'.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(profit') = len(profit); and for every i with 0 <= i < len(difficulty), 1 <= profit[i] <= profit'[i] <= 100000. -/
theorem spec_11 (difficulty profit profit' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp'_len : profit'.val.length = profit.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) profit.val profit'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit' worker = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (difficulty profit profit' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp'_len : profit'.val.length = profit.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) profit.val profit'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty profit' worker = ok r'), r.val ≤ r'.val) := by
  sorry

/-- Let r be the result of the function on (difficulty, profit, worker) and r' the result on (difficulty', profit, worker). Whenever both calls return results, r' <= r.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; len(difficulty') = len(difficulty); and for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= difficulty'[i] <= 100000. -/
theorem spec_12 (difficulty profit difficulty' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd'_len : difficulty'.val.length = difficulty.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) difficulty.val difficulty'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty' profit worker = ok r') :
    r'.val ≤ r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (difficulty profit difficulty' worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd'_len : difficulty'.val.length = difficulty.val.length)
    (hle : List.Forall₂ (fun a b => a.val ≤ b.val) difficulty.val difficulty'.val)
    (r r' : I64)
    (hr : max_profit_assignment difficulty profit worker = ok r)
    (hr' : max_profit_assignment difficulty' profit worker = ok r'), r'.val ≤ r.val) := by
  sorry

/-- Let C be the number of j with 0 <= j < len(worker) for which there exists i with 0 <= i < len(difficulty) and difficulty[i] <= worker[j]. Whenever the function returns a result r, r = p * C.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; and there exists an integer p such that profit[i] = p for every 0 <= i < len(difficulty). -/
theorem spec_13 (difficulty profit worker : Slice I64) (p : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp : ∀ x ∈ profit.val, x.val = p)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    r.val = p * (countAffordable difficulty worker : Int) := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (difficulty profit worker : Slice I64) (p : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hp : ∀ x ∈ profit.val, x.val = p)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), r.val = p * (countAffordable difficulty worker : Int)) := by
  sorry

/-- Let P = max{ profit[i] | 0 <= i < len(difficulty) }, and let C be the number of j with 0 <= j < len(worker) and worker[j] >= d. Whenever the function returns a result r, r = P * C.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000; and there exists an integer d such that difficulty[i] = d for every 0 <= i < len(difficulty). -/
theorem spec_14 (difficulty profit worker : Slice I64) (d : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd : ∀ x ∈ difficulty.val, x.val = d)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    r.val = maxProfit profit * (countAtLeast worker d : Int) := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (difficulty profit worker : Slice I64) (d : Int)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hd : ∀ x ∈ difficulty.val, x.val = d)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), r.val = maxProfit profit * (countAtLeast worker d : Int)) := by
  sorry

/-- Whenever the function returns a result r, the following hold: (1) there exists a feasible assignment, meaning a choice for each j with 0 <= j < len(worker) of either no job or an index i_j with 0 <= i_j < len(difficulty) and difficulty[i_j] <= worker[j], such that the assignment's total profit, defined as the sum of profit[i_j] over workers assigned a job and 0 for unassigned workers, equals r, and moreover if no job is chosen for j then there is no i with 0 <= i < len(difficulty) and difficulty[i] <= worker[j]; and (2) for every feasible assignment (where a worker may choose no job even if some affordable job exists), its total profit is at most r.
  Preconditions: len(difficulty) = len(profit); 1 <= len(difficulty) <= 10000; 1 <= len(worker) <= 10000; for every i with 0 <= i < len(difficulty), 1 <= difficulty[i] <= 100000 and 1 <= profit[i] <= 100000; and for every j with 0 <= j < len(worker), 1 <= worker[j] <= 100000. -/
theorem spec_15 (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r) :
    (∃ a : Nat → Option Nat,
        FeasibleAssignment difficulty worker a ∧
        UsesJobWhenPossible difficulty worker a ∧
        assignmentProfit profit worker.val.length a = r.val) ∧
      (∀ a : Nat → Option Nat, FeasibleAssignment difficulty worker a →
        assignmentProfit profit worker.val.length a ≤ r.val) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (difficulty profit worker : Slice I64)
    (hlen : difficulty.val.length = profit.val.length)
    (hn_lo : 1 ≤ difficulty.val.length) (hn_hi : difficulty.val.length ≤ 10000)
    (hm_lo : 1 ≤ worker.val.length) (hm_hi : worker.val.length ≤ 10000)
    (hdiff : ∀ x ∈ difficulty.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hprof : ∀ x ∈ profit.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (hwork : ∀ x ∈ worker.val, 1 ≤ x.val ∧ x.val ≤ 100000)
    (r : I64) (hr : max_profit_assignment difficulty profit worker = ok r), (∃ a : Nat → Option Nat,
        FeasibleAssignment difficulty worker a ∧
        UsesJobWhenPossible difficulty worker a ∧
        assignmentProfit profit worker.val.length a = r.val) ∧
      (∀ a : Nat → Option Nat, FeasibleAssignment difficulty worker a →
        assignmentProfit profit worker.val.length a ≤ r.val)) := by
  sorry

end AegisSpec.MaxProfitAssignment
