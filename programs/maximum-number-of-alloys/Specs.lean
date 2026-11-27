import Aegis.MaxNumberOfAlloys.Code.Funs

/-!
# Specifications of `Aegis.MaxNumberOfAlloys.max_number_of_alloys`

LeetCode problem `maximum-number-of-alloys`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MaxNumberOfAlloys

namespace AegisSpec.MaxNumberOfAlloys

abbrev I64 := Aeneas.Std.I64

abbrev I64Slice := Aeneas.Std.Slice Aeneas.Std.I64

abbrev CompMatrix := Aeneas.Std.Slice (Aeneas.Std.alloc.vec.Vec Aeneas.Std.I64)

def ints (l : List I64) : List ℤ := l.map (fun x => x.val)

def vals (l : I64Slice) : List ℤ := ints l.val

def entry (l : I64Slice) (j : ℤ) : ℤ := (vals l).getD j.toNat 0

def compRows (composition : CompMatrix) : List (List ℤ) :=
  composition.val.map (fun v => ints v.val)

def compRow (composition : CompMatrix) (i : ℤ) : List ℤ :=
  (compRows composition).getD i.toNat []

def compAt (composition : CompMatrix) (i j : ℤ) : ℤ := (compRow composition i).getD j.toNat 0

def costOf (comp stock cost : List ℤ) (x : ℤ) : ℤ :=
  ((List.range comp.length).map (fun j =>
      max 0 (x * comp.getD j 0 - stock.getD j 0) * cost.getD j 0)).sum

def costAt (composition : CompMatrix) (stock cost : I64Slice) (i x : ℤ) : ℤ :=
  costOf (compRow composition i) (vals stock) (vals cost) x

def Feasible (composition : CompMatrix) (stock cost : I64Slice) (budget k x : ℤ) : Prop :=
  ∃ i : ℤ, 0 ≤ i ∧ i < k ∧ costAt composition stock cost i x ≤ budget

def listMin (d : ℤ) : List ℤ → ℤ
  | [] => d
  | a :: l => l.foldl min a

def listMax (d : ℤ) : List ℤ → ℤ
  | [] => d
  | a :: l => l.foldl max a

def minStockRatio (comp stock : List ℤ) : ℤ :=
  listMin 0 ((List.range comp.length).map (fun j => stock.getD j 0 / comp.getD j 0))

def maxMinStockRatio (composition : CompMatrix) (stock : I64Slice) : ℤ :=
  listMax 0 ((compRows composition).map (fun comp => minStockRatio comp (vals stock)))

def minStockPlusBudgetRatio (comp stock : List ℤ) (budget : ℤ) : ℤ :=
  listMin 0 ((List.range comp.length).map (fun j => (stock.getD j 0 + budget) / comp.getD j 0))

def maxMinStockPlusBudgetRatio (composition : CompMatrix) (stock : I64Slice) (budget : ℤ) : ℤ :=
  listMax 0 ((compRows composition).map (fun comp =>
    minStockPlusBudgetRatio comp (vals stock) budget))

def RowsPermuted (π : ℤ → ℤ) (a b : List (List ℤ)) : Prop :=
  (∀ i : ℤ, 0 ≤ i → i < (a.length : ℤ) → 0 ≤ π i ∧ π i < (a.length : ℤ)) ∧
  (∀ i j : ℤ, 0 ≤ i → i < (a.length : ℤ) → 0 ≤ j → j < (a.length : ℤ) → π i = π j → i = j) ∧
  b.length = a.length ∧
  (∀ i : ℤ, 0 ≤ i → i < (a.length : ℤ) → b.getD i.toNat [] = a.getD (π i).toNat [])

/-- Let cost_i(x) = sum_{j=0}^{n-1} max(0, x*composition[i][j] - stock[j]) * cost[j] for an integer x >= 0 and 0 <= i < k. The function returns a result r and, interpreting r as a nonnegative integer, r = max { x in N | there exists i with 0 <= i < k and cost_i(x) <= budget }.
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_1 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100) :
    ∃ r : I64,
      Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r ∧
        IsGreatest { x : ℤ | 0 ≤ x ∧ Feasible composition stock cost budget.val k.val x } r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100), ∃ r : I64,
      Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r ∧
        IsGreatest { x : ℤ | 0 ≤ x ∧ Feasible composition stock cost budget.val k.val x } r.val) := by
  sorry

/-- The function returns a result r; it does not fail due to arithmetic overflow, out-of-bounds access, or panic.
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_2 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100) :
    ∃ r : I64,
      Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100), ∃ r : I64,
      Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) := by
  sorry

/-- Whenever the function returns a result r, there exists an index i with 0 <= i < k such that sum_{j=0}^{n-1} max(0, r*composition[i][j] - stock[j]) * cost[j] <= budget.
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_3 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) :
    Feasible composition stock cost budget.val k.val r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r), Feasible composition stock cost budget.val k.val r.val) := by
  sorry

/-- Whenever the function returns a result r, for every i with 0 <= i < k, sum_{j=0}^{n-1} max(0, (r+1)*composition[i][j] - stock[j]) * cost[j] > budget.
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_4 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) :
    ∀ i : ℤ, 0 ≤ i → i < k.val →
      costAt composition stock cost i (r.val + 1) > budget.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r), ∀ i : ℤ, 0 ≤ i → i < k.val →
      costAt composition stock cost i (r.val + 1) > budget.val) := by
  sorry

/-- Whenever the function returns a result r, r >= max_{0 <= i < k} min_{0 <= j < n} floor(stock[j] / composition[i][j]).
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_5 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) :
    maxMinStockRatio composition stock ≤ r.val := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r), maxMinStockRatio composition stock ≤ r.val) := by
  sorry

/-- Whenever the function returns a result r, r <= max_{0 <= i < k} min_{0 <= j < n} floor((stock[j] + budget) / composition[i][j]).
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_6 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) :
    r.val ≤ maxMinStockPlusBudgetRatio composition stock budget.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r), r.val ≤ maxMinStockPlusBudgetRatio composition stock budget.val) := by
  sorry

/-- Whenever the function returns a result r, r = 0 if and only if for every i with 0 <= i < k, sum_{j=0}^{n-1} max(0, composition[i][j] - stock[j]) * cost[j] > budget.
  Preconditions: n, k, and budget are the I64 parameters interpreted as mathematical integers, with 1 <= n <= 100, 1 <= k <= 100, and 0 <= budget <= 10^8. The length of composition equals the integer k, and for every i with 0 <= i < k, the length of composition[i] equals the integer n. The lengths of stock and cost both equal n. For every j with 0 <= j < n, 0 <= stock[j] <= 10^8 and 1 <= cost[j] <= 100. For every i,j with 0 <= i < k and 0 <= j < n, 1 <= composition[i][j] <= 100. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_7 (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r) :
    (r.val = 0 ↔
      ∀ i : ℤ, 0 ≤ i → i < k.val → costAt composition stock cost i 1 > budget.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n k budget : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (r : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r), (r.val = 0 ↔
      ∀ i : ℤ, 0 ≤ i → i < k.val → costAt composition stock cost i 1 > budget.val)) := by
  sorry

/-- If max_number_of_alloys(n,k,b1,composition,stock,cost) returns r1 and max_number_of_alloys(n,k,b2,composition,stock,cost) returns r2, then r1 <= r2.
  Preconditions: Fix n,k,composition,stock,cost satisfying the length and value constraints from the problem: 1 <= n <= 100, 1 <= k <= 100, len(composition)=k, each composition[i] has length n, len(stock)=len(cost)=n, 0 <= stock[j] <= 10^8, 1 <= cost[j] <= 100, and 1 <= composition[i][j] <= 100. Let b1 and b2 be integers with 0 <= b1 <= b2 <= 10^8. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_8 (n k b1 b2 : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (hb1_lo : 0 ≤ b1.val) (hb12 : b1.val ≤ b2.val) (hb2_hi : b2.val ≤ 10 ^ 8)
    (r1 r2 : I64)
    (h1 : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k b1 composition stock cost = ok r1)
    (h2 : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k b2 composition stock cost = ok r2) :
    r1.val ≤ r2.val := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n k b1 b2 : I64) (composition : CompMatrix) (stock cost : I64Slice)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (hb1_lo : 0 ≤ b1.val) (hb12 : b1.val ≤ b2.val) (hb2_hi : b2.val ≤ 10 ^ 8)
    (r1 r2 : I64)
    (h1 : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k b1 composition stock cost = ok r1)
    (h2 : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k b2 composition stock cost = ok r2), r1.val ≤ r2.val) := by
  sorry

/-- If max_number_of_alloys(n,k,budget,composition,stock,cost) returns r and max_number_of_alloys(n,k,budget,composition_pi,stock,cost) returns r_pi, then r = r_pi.
  Preconditions: Fix n,k,budget,composition,stock,cost satisfying the full problem constraints (as in spec_1), and let pi be any bijection from {0,...,k-1} to itself. Define composition_pi by composition_pi[i] = composition[pi(i)] for 0 <= i < k; it also satisfies the same constraints. All indices in the specification are 0-based; arithmetic in formulas is ordinary mathematical integer arithmetic. -/
theorem spec_9 (n k budget : I64) (composition composition_pi : CompMatrix)
    (stock cost : I64Slice) (π : ℤ → ℤ)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (hperm : RowsPermuted π (compRows composition) (compRows composition_pi))
    (r r_pi : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r)
    (hr_pi : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition_pi stock cost
      = ok r_pi) :
    r = r_pi := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n k budget : I64) (composition composition_pi : CompMatrix)
    (stock cost : I64Slice) (π : ℤ → ℤ)
    (hn_lo : 1 ≤ n.val) (hn_hi : n.val ≤ 100)
    (hk_lo : 1 ≤ k.val) (hk_hi : k.val ≤ 100)
    (hbudget_lo : 0 ≤ budget.val) (hbudget_hi : budget.val ≤ 10 ^ 8)
    (hlen_composition : (compRows composition).length = k.val.toNat)
    (hlen_rows : ∀ v ∈ compRows composition, v.length = n.val.toNat)
    (hlen_stock : stock.val.length = n.val.toNat)
    (hlen_cost : cost.val.length = n.val.toNat)
    (hstock_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 0 ≤ entry stock j ∧ entry stock j ≤ 10 ^ 8)
    (hcost_bounds : ∀ j : ℤ, 0 ≤ j → j < n.val → 1 ≤ entry cost j ∧ entry cost j ≤ 100)
    (hcomposition_bounds : ∀ i j : ℤ, 0 ≤ i → i < k.val → 0 ≤ j → j < n.val →
      1 ≤ compAt composition i j ∧ compAt composition i j ≤ 100)
    (hperm : RowsPermuted π (compRows composition) (compRows composition_pi))
    (r r_pi : I64)
    (hr : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition stock cost = ok r)
    (hr_pi : Aegis.MaxNumberOfAlloys.max_number_of_alloys n k budget composition_pi stock cost
      = ok r_pi), r = r_pi) := by
  sorry

end AegisSpec.MaxNumberOfAlloys
