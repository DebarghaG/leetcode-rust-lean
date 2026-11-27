import Aegis.PaintWalls.Code.Funs

/-!
# Specifications of `Aegis.PaintWalls.paint_walls`

LeetCode problem `painting-the-walls`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.PaintWalls

namespace AegisSpec.PaintWalls

def entryAt (l : List I64) (i : Nat) : Int := ((l[i]?).map (fun x => x.val)).getD 0

def costAt (cost : Slice I64) (i : Nat) : Int := entryAt cost.val i

def timeAt (time : Slice I64) (i : Nat) : Int := entryAt time.val i

def indexSet (n : Nat) : Finset Nat := Finset.range n

def Feasible (time : Slice I64) (n : Nat) (S : Finset Nat) : Prop :=
  S ⊆ indexSet n ∧ (S.card : Int) + (∑ i ∈ S, timeAt time i) ≥ (n : Int)

def costSum (cost : Slice I64) (S : Finset Nat) : Int := ∑ i ∈ S, costAt cost i

def achievableCosts (cost time : Slice I64) (n : Nat) : Set Int :=
  {v | ∃ S : Finset Nat, Feasible time n S ∧ v = costSum cost S}

def achievableCards (time : Slice I64) (n : Nat) : Set Nat :=
  {m | ∃ S : Finset Nat, Feasible time n S ∧ m = S.card}

def balancedCosts (cost : Slice I64) (n : Nat) : Set Int :=
  {v | ∃ S : Finset Nat, S ⊆ indexSet n ∧ S.card = (n + 1) / 2 ∧ v = costSum cost S}

def Constraints (cost time : Slice I64) (n : Nat) : Prop :=
  n = cost.val.length ∧ time.val.length = n ∧ 1 ≤ n ∧ n ≤ 500 ∧
    (∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000) ∧
    (∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)

/-- The function returns a result r and r = min{ sum_{i in S} cost[i] : S is a subset of {0,...,n-1} and |S| + sum_{i in S} time[i] >= n }.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. All subsets below are subsets of {0,...,n-1}, and |S| denotes the number of elements of S. -/
theorem spec_1 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64, paint_walls cost time = ok r ∧ IsLeast (achievableCosts cost time n) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64, paint_walls cost time = ok r ∧ IsLeast (achievableCosts cost time n) r.val) := by
  sorry

/-- The function returns a result r; it does not fail, overflow, go out of bounds, or panic.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_2 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64, paint_walls cost time = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64, paint_walls cost time = ok r) := by
  sorry

/-- The function returns a result r and there exists a subset S of {0,...,n-1} with |S| + sum_{i in S} time[i] >= n such that r = sum_{i in S} cost[i].
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. All subsets below are subsets of {0,...,n-1}. -/
theorem spec_3 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∃ S : Finset Nat, Feasible time n S ∧ r.val = costSum cost S := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∃ S : Finset Nat, Feasible time n S ∧ r.val = costSum cost S) := by
  sorry

/-- The function returns a result r and for every subset S of {0,...,n-1} with |S| + sum_{i in S} time[i] >= n, r <= sum_{i in S} cost[i].
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. All subsets below are subsets of {0,...,n-1}. -/
theorem spec_4 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∀ S : Finset Nat, Feasible time n S → r.val ≤ costSum cost S := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∀ S : Finset Nat, Feasible time n S → r.val ≤ costSum cost S) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} cost[i].
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_5 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64, paint_walls cost time = ok r ∧ r.val ≤ ∑ i ∈ indexSet n, costAt cost i := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64, paint_walls cost time = ok r ∧ r.val ≤ ∑ i ∈ indexSet n, costAt cost i) := by
  sorry

/-- The function returns a result r and r >= min{ cost[i] : 0 <= i < n }.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_6 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64, paint_walls cost time = ok r ∧ ∃ i : Nat, i < n ∧ costAt cost i ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64, paint_walls cost time = ok r ∧ ∃ i : Nat, i < n ∧ costAt cost i ≤ r.val) := by
  sorry

/-- The function returns a result r, and if the set A = { i : 0 <= i < n and time[i] >= n - 1 } is nonempty, then r <= min{ cost[i] : i in A }.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_7 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧
        ((∃ i : Nat, i < n ∧ (n : Int) - 1 ≤ timeAt time i) →
          ∀ i : Nat, i < n → (n : Int) - 1 ≤ timeAt time i → r.val ≤ costAt cost i) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧
        ((∃ i : Nat, i < n ∧ (n : Int) - 1 ≤ timeAt time i) →
          ∀ i : Nat, i < n → (n : Int) - 1 ≤ timeAt time i → r.val ≤ costAt cost i)) := by
  sorry

/-- The function returns a result r, and if n = 1, then r = cost[0].
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_8 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64, paint_walls cost time = ok r ∧ (n = 1 → r.val = costAt cost 0) := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64, paint_walls cost time = ok r ∧ (n = 1 → r.val = costAt cost 0)) := by
  sorry

/-- The function returns a result r, and if n = 2, then r = min(cost[0], cost[1]).
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. -/
theorem spec_9 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧ (n = 2 → r.val = min (costAt cost 0) (costAt cost 1)) := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧ (n = 2 → r.val = min (costAt cost 0) (costAt cost 1))) := by
  sorry

/-- The function returns a result r, and if there exists an integer c such that cost[i] = c for every i with 0 <= i < n, then r = c * m, where m = min{ |S| : S subset of {0,...,n-1} and |S| + sum_{i in S} time[i] >= n }.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. All subsets below are subsets of {0,...,n-1}. -/
theorem spec_10 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∀ c : Int, (∀ i : Nat, i < n → costAt cost i = c) →
          ∀ m : Nat, IsLeast (achievableCards time n) m → r.val = c * (m : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧
        ∀ c : Int, (∀ i : Nat, i < n → costAt cost i = c) →
          ∀ m : Nat, IsLeast (achievableCards time n) m → r.val = c * (m : Int)) := by
  sorry

/-- The function returns a result r, and if time[i] = 1 for every i with 0 <= i < n, then r = min{ sum_{i in S} cost[i] : S subset of {0,...,n-1} and |S| = ceil(n / 2) }.
  Preconditions: Let n = len(cost). The input satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. All subsets below are subsets of {0,...,n-1}. -/
theorem spec_11 (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500) :
    ∃ r : I64,
      paint_walls cost time = ok r ∧
        ((∀ i : Nat, i < n → timeAt time i = 1) → IsLeast (balancedCosts cost n) r.val) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cost time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500), ∃ r : I64,
      paint_walls cost time = ok r ∧
        ((∀ i : Nat, i < n → timeAt time i = 1) → IsLeast (balancedCosts cost n) r.val)) := by
  sorry

/-- Whenever the function returns r on (cost,time) and returns r2 on (cost2,time), r <= r2.
  Preconditions: Let n = len(cost). The input (cost,time) satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. Also let cost2 be any array of n integers such that 1 <= cost2[i] <= 1000000 for every i and cost[i] <= cost2[i] for every i. -/
theorem spec_12 (cost cost2 time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : cost2.val.length = n)
    (hcost2 : ∀ i : Nat, i < n → 1 ≤ costAt cost2 i ∧ costAt cost2 i ≤ 1000000)
    (hmono : ∀ i : Nat, i < n → costAt cost i ≤ costAt cost2 i) :
    ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost2 time = ok r2 → r.val ≤ r2.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cost cost2 time : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : cost2.val.length = n)
    (hcost2 : ∀ i : Nat, i < n → 1 ≤ costAt cost2 i ∧ costAt cost2 i ≤ 1000000)
    (hmono : ∀ i : Nat, i < n → costAt cost i ≤ costAt cost2 i), ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost2 time = ok r2 → r.val ≤ r2.val) := by
  sorry

/-- Whenever the function returns r on (cost,time) and returns r2 on (cost,time2), r2 <= r.
  Preconditions: Let n = len(cost). The input (cost,time) satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. Also let time2 be any array of n integers such that 1 <= time2[i] <= 500 for every i and time[i] <= time2[i] for every i. -/
theorem spec_13 (cost time time2 : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : time2.val.length = n)
    (htime2 : ∀ i : Nat, i < n → 1 ≤ timeAt time2 i ∧ timeAt time2 i ≤ 500)
    (hmono : ∀ i : Nat, i < n → timeAt time i ≤ timeAt time2 i) :
    ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost time2 = ok r2 → r2.val ≤ r.val := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cost time time2 : Slice I64) (n : Nat) (hn : n = cost.val.length)
    (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : time2.val.length = n)
    (htime2 : ∀ i : Nat, i < n → 1 ≤ timeAt time2 i ∧ timeAt time2 i ≤ 500)
    (hmono : ∀ i : Nat, i < n → timeAt time i ≤ timeAt time2 i), ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost time2 = ok r2 → r2.val ≤ r.val) := by
  sorry

/-- Whenever the function returns r on (cost,time) and returns r2 on (cost2,time2), r = r2.
  Preconditions: Let n = len(cost). The input (cost,time) satisfies the problem constraints: len(time) = n, 1 <= n <= 500, and for every i with 0 <= i < n, 1 <= cost[i] <= 1000000 and 1 <= time[i] <= 500. Let p be any permutation of {0,...,n-1}, and define cost2[i] = cost[p(i)] and time2[i] = time[p(i)] for every 0 <= i < n. -/
theorem spec_14 (cost time cost2 time2 : Slice I64) (n : Nat) (p : Equiv.Perm (Fin n))
    (hn : n = cost.val.length) (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : cost2.val.length = n) (hlen3 : time2.val.length = n)
    (hcost2 : ∀ i : Fin n, costAt cost2 i.val = costAt cost (p i).val)
    (htime2 : ∀ i : Fin n, timeAt time2 i.val = timeAt time (p i).val) :
    ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost2 time2 = ok r2 → r.val = r2.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (cost time cost2 time2 : Slice I64) (n : Nat) (p : Equiv.Perm (Fin n))
    (hn : n = cost.val.length) (hlen : time.val.length = n) (hnpos : 1 ≤ n) (hnle : n ≤ 500)
    (hcost : ∀ i : Nat, i < n → 1 ≤ costAt cost i ∧ costAt cost i ≤ 1000000)
    (htime : ∀ i : Nat, i < n → 1 ≤ timeAt time i ∧ timeAt time i ≤ 500)
    (hlen2 : cost2.val.length = n) (hlen3 : time2.val.length = n)
    (hcost2 : ∀ i : Fin n, costAt cost2 i.val = costAt cost (p i).val)
    (htime2 : ∀ i : Fin n, timeAt time2 i.val = timeAt time (p i).val), ∀ r r2 : I64, paint_walls cost time = ok r → paint_walls cost2 time2 = ok r2 → r.val = r2.val) := by
  sorry

end AegisSpec.PaintWalls
