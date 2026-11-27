import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `minimum-cost-to-make-array-equal`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCost

open Aegis.MinCost

def absI (z : Int) : Int := if z < 0 then -z else z

def nthVal (l : List I64) (i : Nat) : Int := (l.getD i 0#i64).val

def objVal (nums cost : List I64) (x : Int) : Int :=
  (List.zipWith (fun (a c : I64) => c.val * absI (a.val - x)) nums cost).sum

def totalCost (cost : List I64) : Int := (cost.map (fun (c : I64) => c.val)).sum

def costLt (nums cost : List I64) (x : Int) : Int :=
  (List.zipWith (fun (a c : I64) => if a.val < x then c.val else 0) nums cost).sum

def costGt (nums cost : List I64) (x : Int) : Int :=
  (List.zipWith (fun (a c : I64) => if x < a.val then c.val else 0) nums cost).sum

def IsMinValue (f : Int → Int) (r : Int) : Prop :=
  (∀ x : Int, r ≤ f x) ∧ ∃ x : Int, f x = r

def valsOf (l : List I64) : List Int := l.map (fun (a : I64) => a.val)

def lmin : List Int → Int
  | [] => 0
  | a :: l => l.foldl (fun (m : Int) (b : Int) => if b < m then b else m) a

def lmax : List Int → Int
  | [] => 0
  | a :: l => l.foldl (fun (m : Int) (b : Int) => if m < b then b else m) a

def gcdOf (l : List I64) : Nat :=
  l.foldl (fun (g : Nat) (c : I64) => Nat.gcd g c.val.natAbs) 0

/-- The function returns a result r and r = min { sum_{i=0}^{n-1} cost[i] * |nums[i] - x| : x ∈ Z }, where |a| denotes the absolute value of a.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_1 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      IsMinValue (fun x : Int => objVal nums.val cost.val x) r.val := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      IsMinValue (fun x : Int => objVal nums.val cost.val x) r.val) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: len(nums) = len(cost) = n, n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6, and there exists an integer v such that for every i with 0 <= i < n, nums[i] = v. -/
theorem spec_2 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_const : ∃ v : Int, ∀ i : Nat, i < n → nthVal nums.val i = v) :
    ∃ r : I64, min_cost nums cost = ok r ∧ r.val = 0 := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_const : ∃ v : Int, ∀ i : Nat, i < n → nthVal nums.val i = v), ∃ r : I64, min_cost nums cost = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r = min(cost[0], cost[1]) * |nums[0] - nums[1]|.
  Preconditions: len(nums) = len(cost) = n, n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6, and n = 2. -/
theorem spec_3 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_two : n = 2) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      r.val = min (nthVal cost.val 0) (nthVal cost.val 1) *
        absI (nthVal nums.val 0 - nthVal nums.val 1) := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_two : n = 2), ∃ r : I64, min_cost nums cost = ok r ∧
      r.val = min (nthVal cost.val 0) (nthVal cost.val 1) *
        absI (nthVal nums.val 0 - nthVal nums.val 1)) := by
  sorry

/-- The function returns a result r and r = min { sum_{i=0}^{n-1} cost[i] * |nums[i] - nums[j]| : 0 <= j < n }.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_4 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ j : Nat, j < n → r.val ≤ objVal nums.val cost.val (nthVal nums.val j)) ∧
      (∃ j : Nat, j < n ∧ objVal nums.val cost.val (nthVal nums.val j) = r.val) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ j : Nat, j < n → r.val ≤ objVal nums.val cost.val (nthVal nums.val j)) ∧
      (∃ j : Nat, j < n ∧ objVal nums.val cost.val (nthVal nums.val j) = r.val)) := by
  sorry

/-- The function returns a result r and for every integer x, sum_{i=0}^{n-1} cost[i] * |nums[i] - x| >= r.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_5 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ x : Int, objVal nums.val cost.val x ≥ r.val) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ x : Int, objVal nums.val cost.val x ≥ r.val)) := by
  sorry

/-- The function returns a result r and there exists an integer x with min(nums) <= x <= max(nums) such that sum_{i=0}^{n-1} cost[i] * |nums[i] - x| = r, where min(nums) = min_{0<=i<n} nums[i] and max(nums) = max_{0<=i<n} nums[i].
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_6 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      ∃ x : Int, lmin (valsOf nums.val) ≤ x ∧ x ≤ lmax (valsOf nums.val) ∧
        objVal nums.val cost.val x = r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      ∃ x : Int, lmin (valsOf nums.val) ≤ x ∧ x ≤ lmax (valsOf nums.val) ∧
        objVal nums.val cost.val x = r.val) := by
  sorry

/-- The function returns a result r and there exists an integer x such that sum_{i=0}^{n-1} cost[i] * |nums[i] - x| = r and (sum_{i: nums[i] < x} cost[i] <= (1/2) * sum_{i=0}^{n-1} cost[i]) and (sum_{i: nums[i] > x} cost[i] <= (1/2) * sum_{i=0}^{n-1} cost[i]).
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_7 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      ∃ x : Int, objVal nums.val cost.val x = r.val ∧
        2 * costLt nums.val cost.val x ≤ totalCost cost.val ∧
        2 * costGt nums.val cost.val x ≤ totalCost cost.val := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      ∃ x : Int, objVal nums.val cost.val x = r.val ∧
        2 * costLt nums.val cost.val x ≤ totalCost cost.val ∧
        2 * costGt nums.val cost.val x ≤ totalCost cost.val) := by
  sorry

/-- The function returns a result r on (nums, cost). If nums' is the slice of length n defined by nums'[i] = nums[i] + c for 0 <= i < n, then the function returns r on (nums', cost).
  Preconditions: len(nums) = len(cost) = n, n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6, and let c be any integer such that for all i with 0 <= i < n, 1 <= nums[i] + c <= 10^6. -/
theorem spec_8 (n : Nat) (nums cost nums' : Slice I64) (c : Int)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_shift_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i + c ∧ nthVal nums.val i + c ≤ 1000000)
    (h_nums'_len : nums'.val.length = n)
    (h_nums'_val : ∀ i : Nat, i < n → nthVal nums'.val i = nthVal nums.val i + c)
    (r : I64) (h_res : min_cost nums cost = ok r) :
    min_cost nums' cost = ok r := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (n : Nat) (nums cost nums' : Slice I64) (c : Int)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_shift_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i + c ∧ nthVal nums.val i + c ≤ 1000000)
    (h_nums'_len : nums'.val.length = n)
    (h_nums'_val : ∀ i : Nat, i < n → nthVal nums'.val i = nthVal nums.val i + c)
    (r : I64) (h_res : min_cost nums cost = ok r), min_cost nums' cost = ok r) := by
  sorry

/-- The function returns a result r on (nums, cost). For every permutation π of {0,...,n-1}, if nums' and cost' are the slices of length n defined by nums'[i] = nums[π(i)] and cost'[i] = cost[π(i)] for 0 <= i < n, then the function returns r on (nums', cost').
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_9 (n : Nat) (nums cost nums' cost' : Slice I64) (π : Nat → Nat)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_π_lt : ∀ i : Nat, i < n → π i < n)
    (h_π_inj : ∀ i j : Nat, i < n → j < n → π i = π j → i = j)
    (h_nums'_len : nums'.val.length = n) (h_cost'_len : cost'.val.length = n)
    (h_nums'_val : ∀ i : Nat, i < n → nthVal nums'.val i = nthVal nums.val (π i))
    (h_cost'_val : ∀ i : Nat, i < n → nthVal cost'.val i = nthVal cost.val (π i))
    (r : I64) (h_res : min_cost nums cost = ok r) :
    min_cost nums' cost' = ok r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (n : Nat) (nums cost nums' cost' : Slice I64) (π : Nat → Nat)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_π_lt : ∀ i : Nat, i < n → π i < n)
    (h_π_inj : ∀ i j : Nat, i < n → j < n → π i = π j → i = j)
    (h_nums'_len : nums'.val.length = n) (h_cost'_len : cost'.val.length = n)
    (h_nums'_val : ∀ i : Nat, i < n → nthVal nums'.val i = nthVal nums.val (π i))
    (h_cost'_val : ∀ i : Nat, i < n → nthVal cost'.val i = nthVal cost.val (π i))
    (r : I64) (h_res : min_cost nums cost = ok r), min_cost nums' cost' = ok r) := by
  sorry

/-- The function returns a result r on (nums, cost). If cost' is the slice of length n defined by cost'[i] = k * cost[i] for 0 <= i < n, then the function returns k * r on (nums, cost').
  Preconditions: len(nums) = len(cost) = n, n >= 1, for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6, and let k be a positive integer such that for all i with 0 <= i < n, 1 <= k * cost[i] <= 10^6. -/
theorem spec_10 (n : Nat) (nums cost cost' : Slice I64) (k : Int)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_k : 1 ≤ k)
    (h_kcost_bnd : ∀ i : Nat, i < n → 1 ≤ k * nthVal cost.val i ∧ k * nthVal cost.val i ≤ 1000000)
    (h_cost'_len : cost'.val.length = n)
    (h_cost'_val : ∀ i : Nat, i < n → nthVal cost'.val i = k * nthVal cost.val i)
    (r : I64) (h_res : min_cost nums cost = ok r) :
    ∃ r' : I64, min_cost nums cost' = ok r' ∧ r'.val = k * r.val := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (n : Nat) (nums cost cost' : Slice I64) (k : Int)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_k : 1 ≤ k)
    (h_kcost_bnd : ∀ i : Nat, i < n → 1 ≤ k * nthVal cost.val i ∧ k * nthVal cost.val i ≤ 1000000)
    (h_cost'_len : cost'.val.length = n)
    (h_cost'_val : ∀ i : Nat, i < n → nthVal cost'.val i = k * nthVal cost.val i)
    (r : I64) (h_res : min_cost nums cost = ok r), ∃ r' : I64, min_cost nums cost' = ok r' ∧ r'.val = k * r.val) := by
  sorry

/-- The function returns a result r on (nums, cost). For every array cost' of length n with 1 <= cost'[i] <= 10^6 for all i and cost'[i] >= cost[i] for all i with 0 <= i < n, if the function returns r' on (nums, cost'), then r' >= r.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_11 (n : Nat) (nums cost cost' : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_cost'_len : cost'.val.length = n)
    (h_cost'_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost'.val i ∧ nthVal cost'.val i ≤ 1000000)
    (h_cost'_ge : ∀ i : Nat, i < n → nthVal cost.val i ≤ nthVal cost'.val i)
    (r r' : I64) (h_res : min_cost nums cost = ok r) (h_res' : min_cost nums cost' = ok r') :
    r.val ≤ r'.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (n : Nat) (nums cost cost' : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000)
    (h_cost'_len : cost'.val.length = n)
    (h_cost'_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost'.val i ∧ nthVal cost'.val i ≤ 1000000)
    (h_cost'_ge : ∀ i : Nat, i < n → nthVal cost.val i ≤ nthVal cost'.val i)
    (r r' : I64) (h_res : min_cost nums cost = ok r) (h_res' : min_cost nums cost' = ok r'), r.val ≤ r'.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=0}^{n-1} cost[i] * |nums[i] - nums[0]|.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_12 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      r.val ≤ objVal nums.val cost.val (nthVal nums.val 0) := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      r.val ≤ objVal nums.val cost.val (nthVal nums.val 0)) := by
  sorry

/-- The function returns a result r without failing (no overflow, no out-of-bounds, no panic).
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_13 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r) := by
  sorry

/-- Let g = gcd(cost[0], cost[1], ..., cost[n-1]). The function returns a result r and r is a multiple of g.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_14 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧ ((gcdOf cost.val : Nat) : Int) ∣ r.val := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧ ((gcdOf cost.val : Nat) : Int) ∣ r.val) := by
  sorry

/-- The function returns a result r and r = 0 if and only if there exists an integer v such that for every i with 0 <= i < n, nums[i] = v.
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_15 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      (r.val = 0 ↔ ∃ v : Int, ∀ i : Nat, i < n → nthVal nums.val i = v) := by
  sorry

theorem spec_15_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      (r.val = 0 ↔ ∃ v : Int, ∀ i : Nat, i < n → nthVal nums.val i = v)) := by
  sorry

/-- Let W = sum_{i=0}^{n-1} cost[i]. The function returns a result r and, for every integer x, sum_{i=0}^{n-1} cost[i] * |nums[i] - x| = r if and only if (sum_{i: nums[i] < x} cost[i] <= (1/2) * W and sum_{i: nums[i] > x} cost[i] <= (1/2) * W).
  Preconditions: len(nums) = len(cost) = n, n >= 1, and for every i with 0 <= i < n, 1 <= nums[i] <= 10^6 and 1 <= cost[i] <= 10^6. -/
theorem spec_16 (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000) :
    ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ x : Int, objVal nums.val cost.val x = r.val ↔
        (2 * costLt nums.val cost.val x ≤ totalCost cost.val ∧
         2 * costGt nums.val cost.val x ≤ totalCost cost.val)) := by
  sorry

theorem spec_16_neg :
    ¬ (∀ (n : Nat) (nums cost : Slice I64)
    (h_nums_len : nums.val.length = n) (h_cost_len : cost.val.length = n) (h_n : 1 ≤ n)
    (h_nums_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal nums.val i ∧ nthVal nums.val i ≤ 1000000)
    (h_cost_bnd : ∀ i : Nat, i < n → 1 ≤ nthVal cost.val i ∧ nthVal cost.val i ≤ 1000000), ∃ r : I64, min_cost nums cost = ok r ∧
      (∀ x : Int, objVal nums.val cost.val x = r.val ↔
        (2 * costLt nums.val cost.val x ≤ totalCost cost.val ∧
         2 * costGt nums.val cost.val x ≤ totalCost cost.val))) := by
  sorry

end AegisSpec.MinCost
