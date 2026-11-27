import Aegis.MinSpaceWastedKResizing.Code.Funs

/-!
# Specifications of `Aegis.MinSpaceWastedKResizing.min_space_wasted_k_resizing`

LeetCode problem `minimum-total-space-wasted-with-k-resizing-operations`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result
open Aegis.MinSpaceWastedKResizing

namespace AegisSpec.MinSpaceWastedKResizing

def arrOf (nums : Slice I64) : List Int := nums.val.map (fun x => x.val)

def lenOf (nums : Slice I64) : Nat := (Slice.len nums).val

def sumInts : List Int → Int
  | [] => 0
  | x :: xs => x + sumInts xs

def maxInts : List Int → Int
  | [] => 0
  | x :: xs => max x (maxInts xs)

def segList (l : List Int) (lo hi : Nat) : List Int := (l.drop lo).take (hi + 1 - lo)

def countChanges : List Int → Nat
  | [] => 0
  | [_] => 0
  | x :: y :: ys => (if x = y then 0 else 1) + countChanges (y :: ys)

def totalWaste (a s : List Int) : Int := sumInts (List.zipWith (fun x y => y - x) a s)

def IsValidSizing (a s : List Int) (k : Int) : Prop :=
  s.length = a.length ∧
    (∀ t, t < a.length → a.getD t 0 ≤ s.getD t 0) ∧
    ((countChanges s : Nat) : Int) ≤ k

def IsMinWaste (a : List Int) (k : Int) (m : Int) : Prop :=
  (∃ s, IsValidSizing a s k ∧ totalWaste a s = m) ∧
    ∀ s, IsValidSizing a s k → m ≤ totalWaste a s

def blockCost (a : List Int) (lo hi : Nat) : Int :=
  (((hi + 1 - lo : Nat)) : Int) * maxInts (segList a lo hi) - sumInts (segList a lo hi)

def IsBlockChain (start n : Nat) : List (Nat × Nat) → Prop
  | [] => start = n
  | (lo, hi) :: rest => lo = start ∧ lo ≤ hi ∧ hi < n ∧ IsBlockChain (hi + 1) n rest

def IsPartition (n : Nat) (blocks : List (Nat × Nat)) : Prop := IsBlockChain 0 n blocks

def chainCost (a : List Int) : List (Nat × Nat) → Int
  | [] => 0
  | (lo, hi) :: rest => blockCost a lo hi + chainCost a rest

def IsMinPartitionCostLe (a : List Int) (K : Int) (m : Int) : Prop :=
  (∃ blocks, IsPartition a.length blocks ∧ 1 ≤ ((blocks.length : Nat) : Int) ∧
      ((blocks.length : Nat) : Int) ≤ K ∧ chainCost a blocks = m) ∧
    ∀ blocks, IsPartition a.length blocks → 1 ≤ ((blocks.length : Nat) : Int) →
      ((blocks.length : Nat) : Int) ≤ K → m ≤ chainCost a blocks

def IsMinPartitionCostEq (a : List Int) (K : Int) (m : Int) : Prop :=
  (∃ blocks, IsPartition a.length blocks ∧ ((blocks.length : Nat) : Int) = K ∧
      chainCost a blocks = m) ∧
    ∀ blocks, IsPartition a.length blocks → ((blocks.length : Nat) : Int) = K →
      m ≤ chainCost a blocks

def runLeftLen (s : List Int) (t : Nat) : Nat :=
  ((s.take (t + 1)).reverse.takeWhile (fun x => decide (x = s.getD t 0))).length

def runRightLen (s : List Int) (t : Nat) : Nat :=
  ((s.drop t).takeWhile (fun x => decide (x = s.getD t 0))).length

def runStart (s : List Int) (t : Nat) : Nat := t + 1 - runLeftLen s t

def runEnd (s : List Int) (t : Nat) : Nat := t + runRightLen s t - 1

def RunsTakeMax (a s : List Int) : Prop :=
  ∀ t, t < s.length → s.getD t 0 = maxInts (segList a (runStart s t) (runEnd s t))

def ShiftBy (a a' : List Int) (c : Int) : Prop := a' = a.map (fun x => x + c)

def WfNums (nums : Slice I64) : Prop :=
  1 ≤ lenOf nums ∧ lenOf nums ≤ 200 ∧ ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000000

def WfK (nums : Slice I64) (k : I64) : Prop :=
  0 ≤ k.val ∧ k.val + 1 ≤ ((lenOf nums : Nat) : Int)

/-- Let n = len(nums). A valid sizing is a sequence s_0,...,s_{n-1} of integers such that s_t >= nums[t] for every 0 <= t < n and the number of indices t with 1 <= t < n and s_t != s_{t-1} is at most k. The function returns a result r, and r is the minimum of sum_{t=0}^{n-1} (s_t - nums[t]) over all valid sizings s.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_1 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∃ r, min_space_wasted_k_resizing nums k = ok r ∧ IsMinWaste (arrOf nums) k.val r := by
  sorry

theorem spec_1_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∃ r, min_space_wasted_k_resizing nums k = ok r ∧ IsMinWaste (arrOf nums) k.val r) := by
  sorry

/-- Under the stated preconditions, the function returns a result r and does not fail: no arithmetic overflow, out-of-bounds access, or panic occurs.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_2 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∃ r, min_space_wasted_k_resizing nums k = ok r := by
  sorry

theorem spec_2_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∃ r, min_space_wasted_k_resizing nums k = ok r) := by
  sorry

/-- Let r be the value returned by the function. Then r >= 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_3 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r → 0 ≤ r.val := by
  sorry

theorem spec_3_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r → 0 ≤ r.val) := by
  sorry

/-- Let r be the value returned by the function and let M = max_{0 <= i < n} nums[i]. Then r <= n * M - sum_{t=0}^{n-1} nums[t].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_4 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      r.val ≤ ((lenOf nums : Nat) : Int) * maxInts (arrOf nums) - sumInts (arrOf nums) := by
  sorry

theorem spec_4_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      r.val ≤ ((lenOf nums : Nat) : Int) * maxInts (arrOf nums) - sumInts (arrOf nums)) := by
  sorry

/-- Let r be the value returned by the function and let M = max_{0 <= i < n} nums[i]. Then r = n * M - sum_{t=0}^{n-1} nums[t].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and k = 0. -/
theorem spec_5 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : k.val = 0) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      r.val = ((lenOf nums : Nat) : Int) * maxInts (arrOf nums) - sumInts (arrOf nums) := by
  sorry

theorem spec_5_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : k.val = 0), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      r.val = ((lenOf nums : Nat) : Int) * maxInts (arrOf nums) - sumInts (arrOf nums)) := by
  sorry

/-- Let r be the value returned by the function. Then r = 0.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and k = n-1. -/
theorem spec_6 (nums : Slice I64) (k : I64) (hn : WfNums nums)
    (hk : k.val = ((lenOf nums : Nat) : Int) - 1) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r → r.val = 0 := by
  sorry

theorem spec_6_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums)
    (hk : k.val = ((lenOf nums : Nat) : Int) - 1), ∀ r, min_space_wasted_k_resizing nums k = ok r → r.val = 0) := by
  sorry

/-- Let r be the value returned by the function and let c be the number of indices t with 1 <= t < n and nums[t] != nums[t-1]. Then r = 0 if and only if c <= k.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_7 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      (r.val = 0 ↔ ((countChanges (arrOf nums) : Nat) : Int) ≤ k.val) := by
  sorry

theorem spec_7_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      (r.val = 0 ↔ ((countChanges (arrOf nums) : Nat) : Int) ≤ k.val)) := by
  sorry

/-- Let r be the value returned by the function. For every integer q with 0 <= q <= k, let M_q be the minimum total waste for the same array nums with resize budget q, defined exactly as in the main functional specification. Then r <= M_q.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_8 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∀ q : Int, 0 ≤ q → q ≤ k.val →
        ∀ mq : Int, IsMinWaste (arrOf nums) q mq → r.val ≤ mq := by
  sorry

theorem spec_8_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∀ q : Int, 0 ≤ q → q ≤ k.val →
        ∀ mq : Int, IsMinWaste (arrOf nums) q mq → r.val ≤ mq) := by
  sorry

/-- Let r be the value returned by the function. There exists a sequence s_0,...,s_{n-1} of integers with s_t >= nums[t] for every 0 <= t < n, with at most k indices t in [1,n-1] where s_t != s_{t-1}, and with sum_{t=0}^{n-1} (s_t - nums[t]) = r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_9 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∃ s : List Int, IsValidSizing (arrOf nums) s k.val ∧ totalWaste (arrOf nums) s = r.val := by
  sorry

theorem spec_9_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∃ s : List Int, IsValidSizing (arrOf nums) s k.val ∧ totalWaste (arrOf nums) s = r.val) := by
  sorry

/-- Let r be the value returned by the function. For every sequence s_0,...,s_{n-1} of integers with s_t >= nums[t] for all 0 <= t < n and with at most k changes between consecutive terms, one has sum_{t=0}^{n-1} (s_t - nums[t]) >= r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_10 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∀ s : List Int, IsValidSizing (arrOf nums) s k.val → r.val ≤ totalWaste (arrOf nums) s := by
  sorry

theorem spec_10_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∀ s : List Int, IsValidSizing (arrOf nums) s k.val → r.val ≤ totalWaste (arrOf nums) s) := by
  sorry

/-- Let n = len(nums). For 0 <= l <= r < n define cost(l,r) = (r-l+1) * max_{l <= i <= r} nums[i] - sum_{i=l}^{r} nums[i]. A partition of [0,n) into m blocks is a list [l_0,r_0],...,[l_{m-1},r_{m-1}] with l_0=0, r_{m-1}=n-1, and l_{j+1}=r_j+1 for every 0 <= j < m-1, so every block is nonempty. Let r be the value returned by the function. Then r = min { sum_{j=0}^{m-1} cost(l_j,r_j) : the blocks form a partition of [0,n) and 1 <= m <= k+1 }.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_11 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      IsMinPartitionCostLe (arrOf nums) (k.val + 1) r.val := by
  sorry

theorem spec_11_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      IsMinPartitionCostLe (arrOf nums) (k.val + 1) r.val) := by
  sorry

/-- Let n = len(nums), let m = k+1, and for 0 <= l <= r < n define cost(l,r) = (r-l+1) * max_{l <= i <= r} nums[i] - sum_{i=l}^{r} nums[i]. Let r be the value returned by the function. Then r = min { sum_{j=0}^{m-1} cost(l_j,r_j) : [l_0,r_0],...,[l_{m-1},r_{m-1}] is a partition of [0,n) into m nonempty contiguous blocks }.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_12 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      IsMinPartitionCostEq (arrOf nums) (k.val + 1) r.val := by
  sorry

theorem spec_12_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      IsMinPartitionCostEq (arrOf nums) (k.val + 1) r.val) := by
  sorry

/-- Let r be the value returned by the function. There exists a valid sizing s_0,...,s_{n-1} with s_t >= nums[t] for all 0 <= t < n, with at most k changes between consecutive terms, and with total waste r, such that for every maximal interval [l,r] with 0 <= l <= r < n on which s is constant (s_l = ... = s_r, and either l=0 or s_{l-1} != s_l, and either r=n-1 or s_{r+1} != s_r), the common value s_l equals max_{l <= i <= r} nums[i].
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. -/
theorem spec_13 (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∃ s : List Int, IsValidSizing (arrOf nums) s k.val ∧
        totalWaste (arrOf nums) s = r.val ∧ RunsTakeMax (arrOf nums) s := by
  sorry

theorem spec_13_neg :
    ¬ (∀ (nums : Slice I64) (k : I64) (hn : WfNums nums) (hk : WfK nums k), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      ∃ s : List Int, IsValidSizing (arrOf nums) s k.val ∧
        totalWaste (arrOf nums) s = r.val ∧ RunsTakeMax (arrOf nums) s) := by
  sorry

/-- Let r be the value returned for (nums,k). Let nums' be the array defined by nums'[i] = nums[i] + c for every 0 <= i < n. Then the function called on (nums',k) returns the same value r.
  Preconditions: Let n = len(nums). Assume 1 <= n <= 200, for every i with 0 <= i < n we have 1 <= nums[i] <= 1_000_000, and 0 <= k <= n-1. Let c be an integer such that 1 <= nums[i] + c <= 1_000_000 for every 0 <= i < n. -/
theorem spec_14 (nums nums' : Slice I64) (k : I64) (c : Int) (hn : WfNums nums)
    (hk : WfK nums k) (hc : ∀ x ∈ nums.val, 1 ≤ x.val + c ∧ x.val + c ≤ 1000000)
    (hshift : ShiftBy (arrOf nums) (arrOf nums') c) :
    ∀ r, min_space_wasted_k_resizing nums k = ok r →
      min_space_wasted_k_resizing nums' k = ok r := by
  sorry

theorem spec_14_neg :
    ¬ (∀ (nums nums' : Slice I64) (k : I64) (c : Int) (hn : WfNums nums)
    (hk : WfK nums k) (hc : ∀ x ∈ nums.val, 1 ≤ x.val + c ∧ x.val + c ≤ 1000000)
    (hshift : ShiftBy (arrOf nums) (arrOf nums') c), ∀ r, min_space_wasted_k_resizing nums k = ok r →
      min_space_wasted_k_resizing nums' k = ok r) := by
  sorry

end AegisSpec.MinSpaceWastedKResizing
