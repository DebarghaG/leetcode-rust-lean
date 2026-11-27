import Aegis.MinCosts.Code.Funs

/-!
# Specifications of `Aegis.MinCosts.min_costs`

LeetCode problem `minimum-cost-to-reach-every-position`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCosts

def elemAt (s : List Std.I64) (i : Nat) : Int := (s[i]!).val

def IsPrefixMin (c : List Std.I64) (i : Nat) (v : Int) : Prop :=
  (∀ j : Nat, j ≤ i → v ≤ elemAt c j) ∧ (∃ j : Nat, j ≤ i ∧ v = elemAt c j)

def IsMinOn (c : List Std.I64) (n : Nat) (v : Int) : Prop :=
  (∀ j : Nat, j < n → v ≤ elemAt c j) ∧ (∃ j : Nat, j < n ∧ v = elemAt c j)

theorem elemAt_of_lt (s : List Std.I64) (i : Nat) (h : i < s.length) :
    elemAt s i = (s[i]).val := by
  simp [elemAt, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The function returns a result r (it does not fail). The returned vector has length n, and for every i with 0 <= i < n, r[i] is the minimum of the prefix cost[0..i]: (a) r[i] <= cost[j] for every j with 0 <= j <= i, and (b) there exists j with 0 <= j <= i such that r[i] = cost[j].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. All values are 64-bit signed integers and these bounds are within range. -/
theorem spec_1 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r ∧
        r.val.length = n ∧
          (∀ i : Nat, i < n → IsPrefixMin cost.val i (elemAt r.val i)) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∃ r : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r ∧
        r.val.length = n ∧
          (∀ i : Nat, i < n → IsPrefixMin cost.val i (elemAt r.val i))) := by
  sorry

/-- The function returns a result r; in particular it does not fail, panic, overflow, or go out of bounds on any input satisfying the constraints.
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_2 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∃ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∃ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r) := by
  sorry

/-- Whenever the function returns a result r, len(r) = n = len(cost).
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_3 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r → r.val.length = n ∧ cost.val.length = n := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r → r.val.length = n ∧ cost.val.length = n) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, 1 <= r[i] <= 100.
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_4 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → 1 ≤ elemAt r.val i ∧ elemAt r.val i ≤ 100 := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → 1 ≤ elemAt r.val i ∧ elemAt r.val i ≤ 100) := by
  sorry

/-- Whenever the function returns a result r, r[0] = cost[0].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_5 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      elemAt r.val 0 = elemAt cost.val 0 := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      elemAt r.val 0 = elemAt cost.val 0) := by
  sorry

/-- Whenever the function returns a result r, r[n-1] is the minimum value in the whole array cost: (a) r[n-1] <= cost[j] for every j with 0 <= j < n, and (b) there exists j with 0 <= j < n such that r[n-1] = cost[j].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_6 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      IsMinOn cost.val n (elemAt r.val (n - 1)) := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      IsMinOn cost.val n (elemAt r.val (n - 1))) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, r[i] <= cost[i].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_7 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → elemAt r.val i ≤ elemAt cost.val i := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → elemAt r.val i ≤ elemAt cost.val i) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n, there exists j with 0 <= j <= i such that r[i] = cost[j].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_8 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → ∃ j : Nat, j ≤ i ∧ elemAt r.val i = elemAt cost.val j := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → ∃ j : Nat, j ≤ i ∧ elemAt r.val i = elemAt cost.val j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n and every j with 0 <= j <= i, r[i] <= cost[j].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_9 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → ∀ j : Nat, j ≤ i → elemAt r.val i ≤ elemAt cost.val j := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n → ∀ j : Nat, j ≤ i → elemAt r.val i ≤ elemAt cost.val j) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < n-1, r[i] >= r[i+1].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_10 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n - 1 → elemAt r.val (i + 1) ≤ elemAt r.val i := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ i : Nat, i < n - 1 → elemAt r.val (i + 1) ≤ elemAt r.val i) := by
  sorry

/-- Whenever the function returns a result r, r[0] = cost[0], and for every i with 0 <= i < n-1, r[i+1] = min(r[i], cost[i+1]), where min denotes the smaller of the two i64 values.
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_11 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      elemAt r.val 0 = elemAt cost.val 0 ∧
        ∀ i : Nat, i < n - 1 →
          elemAt r.val (i + 1) = min (elemAt r.val i) (elemAt cost.val (i + 1)) := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      elemAt r.val 0 = elemAt cost.val 0 ∧
        ∀ i : Nat, i < n - 1 →
          elemAt r.val (i + 1) = min (elemAt r.val i) (elemAt cost.val (i + 1))) := by
  sorry

/-- Whenever the function returns a result r, if cost[0] <= cost[j] for every j with 0 <= j < n, then r[i] = cost[0] for every i with 0 <= i < n.
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_12 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      (∀ j : Nat, j < n → elemAt cost.val 0 ≤ elemAt cost.val j) →
        ∀ i : Nat, i < n → elemAt r.val i = elemAt cost.val 0 := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      (∀ j : Nat, j < n → elemAt cost.val 0 ≤ elemAt cost.val j) →
        ∀ i : Nat, i < n → elemAt r.val i = elemAt cost.val 0) := by
  sorry

/-- Whenever the function returns a result r, if there is an index k with 0 <= k < n such that cost[k] < cost[j] for every j with 0 <= j < n and j != k, then for every i with k <= i < n, r[i] = cost[k].
  Preconditions: len(cost) = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100. -/
theorem spec_13 (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100) :
    ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ k : Nat, k < n →
        (∀ j : Nat, j < n → j ≠ k → elemAt cost.val k < elemAt cost.val j) →
          ∀ i : Nat, k ≤ i → i < n → elemAt r.val i = elemAt cost.val k := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (cost : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100), ∀ r : alloc.vec.Vec Std.I64, Aegis.MinCosts.min_costs cost = ok r →
      ∀ k : Nat, k < n →
        (∀ j : Nat, j < n → j ≠ k → elemAt cost.val k < elemAt cost.val j) →
          ∀ i : Nat, k ≤ i → i < n → elemAt r.val i = elemAt cost.val k) := by
  sorry

/-- For any valid cost array cost' of the same length n and any i with 0 <= i < n, whenever min_costs(cost) returns r and min_costs(cost') returns r', if cost[j] = cost'[j] for every j with 0 <= j <= i, then r[i] = r'[i].
  Preconditions: Both cost and cost' are valid inputs: len(cost) = len(cost') = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100 and 1 <= cost'[i] <= 100. -/
theorem spec_14 (cost cost' : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100)
    (hcost' : ∀ i : Nat, i < n → 1 ≤ elemAt cost'.val i ∧ elemAt cost'.val i ≤ 100) :
    ∀ i : Nat, i < n →
      ∀ r r' : alloc.vec.Vec Std.I64,
        Aegis.MinCosts.min_costs cost = ok r →
          Aegis.MinCosts.min_costs cost' = ok r' →
            (∀ j : Nat, j ≤ i → elemAt cost.val j = elemAt cost'.val j) →
              elemAt r.val i = elemAt r'.val i := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (cost cost' : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100)
    (hcost' : ∀ i : Nat, i < n → 1 ≤ elemAt cost'.val i ∧ elemAt cost'.val i ≤ 100), ∀ i : Nat, i < n →
      ∀ r r' : alloc.vec.Vec Std.I64,
        Aegis.MinCosts.min_costs cost = ok r →
          Aegis.MinCosts.min_costs cost' = ok r' →
            (∀ j : Nat, j ≤ i → elemAt cost.val j = elemAt cost'.val j) →
              elemAt r.val i = elemAt r'.val i) := by
  sorry

/-- For any valid cost array cost' of the same length n, whenever min_costs(cost) returns r and min_costs(cost') returns r', if cost[j] <= cost'[j] for every j with 0 <= j < n, then r[i] <= r'[i] for every i with 0 <= i < n.
  Preconditions: Both cost and cost' are valid inputs: len(cost) = len(cost') = n with 1 <= n <= 100, and for every i with 0 <= i < n, 1 <= cost[i] <= 100 and 1 <= cost'[i] <= 100. -/
theorem spec_15 (cost cost' : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100)
    (hcost' : ∀ i : Nat, i < n → 1 ≤ elemAt cost'.val i ∧ elemAt cost'.val i ≤ 100) :
    ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r →
        Aegis.MinCosts.min_costs cost' = ok r' →
          (∀ j : Nat, j < n → elemAt cost.val j ≤ elemAt cost'.val j) →
            ∀ i : Nat, i < n → elemAt r.val i ≤ elemAt r'.val i := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (cost cost' : Slice Std.I64) (n : Nat)
    (hlen : cost.val.length = n) (hlen' : cost'.val.length = n)
    (hn1 : 1 ≤ n) (hn2 : n ≤ 100)
    (hcost : ∀ i : Nat, i < n → 1 ≤ elemAt cost.val i ∧ elemAt cost.val i ≤ 100)
    (hcost' : ∀ i : Nat, i < n → 1 ≤ elemAt cost'.val i ∧ elemAt cost'.val i ≤ 100), ∀ r r' : alloc.vec.Vec Std.I64,
      Aegis.MinCosts.min_costs cost = ok r →
        Aegis.MinCosts.min_costs cost' = ok r' →
          (∀ j : Nat, j < n → elemAt cost.val j ≤ elemAt cost'.val j) →
            ∀ i : Nat, i < n → elemAt r.val i ≤ elemAt r'.val i) := by
  sorry

end AegisSpec.MinCosts
