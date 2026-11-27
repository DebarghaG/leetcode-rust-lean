import Aegis.MinCost.Code.Funs

/-!
# Specifications of `Aegis.MinCost.min_cost`

LeetCode problem `jump-game-viii`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

namespace AegisSpec.MinCost

def sval (s : Slice Std.I64) (i : Nat) : Int := (s.val[i]!).val

def ValidJump (nums : Slice Std.I64) (i j : Nat) : Prop :=
  i < j ∧ j < nums.val.length ∧
    (((sval nums i ≤ sval nums j) ∧ ∀ k, i < k → k < j → sval nums k < sval nums i) ∨
     ((sval nums i > sval nums j) ∧ ∀ k, i < k → k < j → sval nums k ≥ sval nums i))

def ValidPath (nums : Slice Std.I64) (p : List Nat) : Prop :=
  p ≠ [] ∧ p.head? = some 0 ∧ p.getLast? = some (nums.val.length - 1) ∧
    (∀ t, t + 1 < p.length → ValidJump nums (p[t]!) (p[t+1]!))

def pathCost (costs : Slice Std.I64) (p : List Nat) : Int :=
  ((p.drop 1).map (fun i => sval costs i)).sum

def rangeSum (costs : Slice Std.I64) (a b : Nat) : Int :=
  ((List.range (b - a)).map (fun k => sval costs (a + k))).sum

def JumpCountMin (nums : Slice Std.I64) (J : Nat) : Prop :=
  (∃ p, ValidPath nums p ∧ p.length - 1 = J) ∧
    ∀ p, ValidPath nums p → J ≤ p.length - 1

/-- The function returns a result r. Define a valid jump from i to j (0 <= i < j < n) to mean: either (nums[i] <= nums[j] and for every k with i < k < j, nums[k] < nums[i]) or (nums[i] > nums[j] and for every k with i < k < j, nums[k] >= nums[i]). Define a valid path from 0 to n-1 to be a finite sequence p_0,...,p_m with m >= 0, p_0 = 0, p_m = n-1, p_t < p_{t+1} for every 0 <= t < m, and every consecutive pair p_t -> p_{t+1} is a valid jump; its cost is sum_{t=1}^{m} costs[p_t], with the empty sum 0 when m=0. Then r is the minimum cost among all valid paths from 0 to n-1: equivalently, there exists a valid path P from 0 to n-1 with cost(P)=r, and every valid path Q from 0 to n-1 has cost(Q) >= r.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_1 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      (∃ p, ValidPath nums p ∧ pathCost costs p = r.val) ∧
      (∀ p, ValidPath nums p → r.val ≤ pathCost costs p) := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      (∃ p, ValidPath nums p ∧ pathCost costs p = r.val) ∧
      (∀ p, ValidPath nums p → r.val ≤ pathCost costs p)) := by
  sorry

/-- The function returns a result r; it does not fail.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_2 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r) := by
  sorry

/-- The function returns a result r and r = 0.
  Preconditions: Let n = len(nums) = len(costs). Assume n = 1, so len(nums)=1 and len(costs)=1, with 0 <= nums[0] <= 100000 and 0 <= costs[0] <= 100000. -/
theorem spec_3 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn : n = 1)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = 0 := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn : n = 1)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = 0) := by
  sorry

/-- The function returns a result r and r >= costs[n-1].
  Preconditions: Let n = len(nums) = len(costs). Assume 2 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_4 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ sval costs (n - 1) ≤ r.val := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ sval costs (n - 1) ≤ r.val) := by
  sorry

/-- The function returns a result r and r <= sum_{i=1}^{n-1} costs[i], where the sum is 0 when n=1.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_5 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val ≤ rangeSum costs 1 n := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val ≤ rangeSum costs 1 n) := by
  sorry

/-- The function returns a result r and r >= 0.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_6 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ 0 ≤ r.val := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ 0 ≤ r.val) := by
  sorry

/-- The function returns a result r and r = costs[n-1].
  Preconditions: Let n = len(nums) = len(costs). Assume 2 <= n <= 100000 and all nums[i], costs[i] are in [0,100000]. Assume that a valid jump from 0 to n-1 exists, meaning either (nums[0] <= nums[n-1] and for every k with 0 < k < n-1, nums[k] < nums[0]) or (nums[0] > nums[n-1] and for every k with 0 < k < n-1, nums[k] >= nums[0]). -/
theorem spec_7 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (hjump : ValidJump nums 0 (n - 1)) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = sval costs (n - 1) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 2 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (hjump : ValidJump nums 0 (n - 1)), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = sval costs (n - 1)) := by
  sorry

/-- The function returns a result r and r = sum_{i=1}^{n-1} costs[i], where the sum is 0 when n=1.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and all nums[i], costs[i] are in [0,100000]. Assume nums is nondecreasing: for every i with 0 <= i < n-1, nums[i] <= nums[i+1]. -/
theorem spec_8 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (hmono : ∀ i, i + 1 < n → sval nums i ≤ sval nums (i + 1)) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = rangeSum costs 1 n := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (hmono : ∀ i, i + 1 < n → sval nums i ≤ sval nums (i + 1)), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧ r.val = rangeSum costs 1 n) := by
  sorry

/-- The function returns a result r. For every c with 0 <= c <= 100000, let costs' be any slice of length n such that costs'[0] = c and costs'[i] = costs[i] for every i with 1 <= i < n. Whenever min_cost(nums, costs') returns a result r', we have r' = r.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_9 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∀ (c : Int) (costs' : Slice Std.I64),
        0 ≤ c → c ≤ 100000 →
        costs'.val.length = n →
        sval costs' 0 = c →
        (∀ i, 1 ≤ i → i < n → sval costs' i = sval costs i) →
        ∀ r', Aegis.MinCost.min_cost nums costs' = ok r' → r' = r := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∀ (c : Int) (costs' : Slice Std.I64),
        0 ≤ c → c ≤ 100000 →
        costs'.val.length = n →
        sval costs' 0 = c →
        (∀ i, 1 ≤ i → i < n → sval costs' i = sval costs i) →
        ∀ r', Aegis.MinCost.min_cost nums costs' = ok r' → r' = r) := by
  sorry

/-- The function returns a result r. Define a valid jump from i to j (0 <= i < j < n) to mean: either (nums[i] <= nums[j] and for every k with i < k < j, nums[k] < nums[i]) or (nums[i] > nums[j] and for every k with i < k < j, nums[k] >= nums[i]). Let J be the minimum number of jumps m over all finite sequences p_0,...,p_m with p_0=0, p_m=n-1, p_t < p_{t+1} for every 0 <= t < m, and every consecutive pair a valid jump. Then r = c * J.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and all nums[i], costs[i] are in [0,100000]. Assume there is c with 0 <= c <= 100000 such that costs[i] = c for every i with 0 <= i < n. -/
theorem spec_10 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (c : Int) (hc_lo : 0 ≤ c) (hc_hi : c ≤ 100000)
    (hcosts_const : ∀ i, i < n → sval costs i = c) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∃ J, JumpCountMin nums J ∧ r.val = c * (J : Int) := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000)
    (c : Int) (hc_lo : 0 ≤ c) (hc_hi : c ≤ 100000)
    (hcosts_const : ∀ i, i < n → sval costs i = c), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∃ J, JumpCountMin nums J ∧ r.val = c * (J : Int)) := by
  sorry

/-- The function returns a result r. Define a valid jump from i to j (0 <= i < j < n) to mean: either (nums[i] <= nums[j] and for every k with i < k < j, nums[k] < nums[i]) or (nums[i] > nums[j] and for every k with i < k < j, nums[k] >= nums[i]). Then there exists a finite sequence p_0,...,p_m with m >= 0, p_0=0, p_m=n-1, p_t < p_{t+1} for every 0 <= t < m, every p_t -> p_{t+1} a valid jump, and sum_{t=1}^{m} costs[p_t] = r.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_11 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∃ p, ValidPath nums p ∧ pathCost costs p = r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∃ p, ValidPath nums p ∧ pathCost costs p = r.val) := by
  sorry

/-- The function returns a result r. For every finite sequence p_0,...,p_m with m >= 0, p_0=0, p_m=n-1, p_t < p_{t+1} for every 0 <= t < m, and every consecutive pair p_t -> p_{t+1} being a valid jump (defined as: either nums[p_t] <= nums[p_{t+1}] and for every k with p_t < k < p_{t+1}, nums[k] < nums[p_t], or nums[p_t] > nums[p_{t+1}] and for every k with p_t < k < p_{t+1}, nums[k] >= nums[p_t]), we have sum_{t=1}^{m} costs[p_t] >= r.
  Preconditions: Let n = len(nums) = len(costs). Assume 1 <= n <= 100000 and, for every i with 0 <= i < n, 0 <= nums[i] <= 100000 and 0 <= costs[i] <= 100000. -/
theorem spec_12 (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000) :
    ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∀ p, ValidPath nums p → r.val ≤ pathCost costs p := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums costs : Slice Std.I64) (n : Nat)
    (hnums : nums.val.length = n) (hcosts : costs.val.length = n)
    (hn_lo : 1 ≤ n) (hn_hi : n ≤ 100000)
    (hnums_range : ∀ i, i < n → 0 ≤ sval nums i ∧ sval nums i ≤ 100000)
    (hcosts_range : ∀ i, i < n → 0 ≤ sval costs i ∧ sval costs i ≤ 100000), ∃ r, Aegis.MinCost.min_cost nums costs = ok r ∧
      ∀ p, ValidPath nums p → r.val ≤ pathCost costs p) := by
  sorry

end AegisSpec.MinCost
