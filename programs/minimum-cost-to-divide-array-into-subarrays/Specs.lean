import Aegis.MinimumCost.Code.Funs

/-!
# Specifications of `Aegis.MinimumCost.minimum_cost`

LeetCode problem `minimum-cost-to-divide-array-into-subarrays`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinimumCost

  def vals (s : Aeneas.Std.Slice Aeneas.Std.I64) : List ℤ := s.val.map (fun x => x.val)

  def segSum (l : List ℤ) (lo hi : ℕ) : ℤ := ((l.drop lo).take (hi - lo)).sum

  def preSum (l : List ℤ) (hi : ℕ) : ℤ := (l.take hi).sum

  def IsCutSeq (n m : ℕ) (p : ℕ → ℕ) : Prop :=
    p 0 = 0 ∧ p m = n ∧ ∀ t, t < m → p t < p (t + 1)

  def divCost (nums cost : List ℤ) (k : ℤ) (m : ℕ) (p : ℕ → ℕ) : ℤ :=
    ∑ t ∈ Finset.range m,
      (preSum nums (p (t + 1)) + k * ((t : ℤ) + 1)) * segSum cost (p t) (p (t + 1))

  /-- The function returns a result r (it does not fail), and r equals the minimum, over all integers m >= 1 and all cut positions 0 = p_0 < p_1 < ... < p_m = n, of the total cost sum_{t=1}^{m} ( (sum_{q=0}^{p_t-1} nums[q]) + k*t ) * (sum_{q=p_{t-1}}^{p_t-1} cost[q]). Each term is the cost of the t-th subarray nums[p_{t-1} .. p_t-1], with t 1-based; every division into contiguous nonempty subarrays corresponds exactly to such a cut sequence.
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_1 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r ∧
        (∀ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m → IsCutSeq nums.val.length m p →
          r.val ≤ divCost (vals nums) (vals cost) k.val m p) ∧
        (∃ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m ∧ IsCutSeq nums.val.length m p ∧
          r.val = divCost (vals nums) (vals cost) k.val m p) := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∃ r : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r ∧
          (∀ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m → IsCutSeq nums.val.length m p →
            r.val ≤ divCost (vals nums) (vals cost) k.val m p) ∧
          (∃ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m ∧ IsCutSeq nums.val.length m p ∧
            r.val = divCost (vals nums) (vals cost) k.val m p)) := by
    sorry

  /-- For every input satisfying the preconditions, the function returns a result r (a successful Result containing a 64-bit integer); there is no overflow, out-of-bounds access, or panic.
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_2 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∃ r : Aeneas.Std.I64, Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r :=
    by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∃ r : Aeneas.Std.I64, Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r >= (nums[0] + k) * (sum_{i=0}^{n-1} cost[i]).
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_3 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        ((vals nums).headD 0 + k.val) * (vals cost).sum ≤ r.val := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          ((vals nums).headD 0 + k.val) * (vals cost).sum ≤ r.val) := by
    sorry

  /-- Whenever the function returns a result r, 2 <= r <= 1001000000000.
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_4 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        2 ≤ r.val ∧ r.val ≤ 1001000000000 := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          2 ≤ r.val ∧ r.val ≤ 1001000000000) := by
    sorry

  /-- Whenever the function returns a result r, there exist an integer m >= 1 and cut positions 0 = p_0 < p_1 < ... < p_m = n such that r = sum_{t=1}^{m} ( (sum_{q=0}^{p_t-1} nums[q]) + k*t ) * (sum_{q=p_{t-1}}^{p_t-1} cost[q]).
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_5 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        ∃ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m ∧ IsCutSeq nums.val.length m p ∧
          r.val = divCost (vals nums) (vals cost) k.val m p := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          ∃ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m ∧ IsCutSeq nums.val.length m p ∧
            r.val = divCost (vals nums) (vals cost) k.val m p) := by
    sorry

  /-- Whenever the function returns a result r, for every integer m >= 1 and every cut positions 0 = p_0 < p_1 < ... < p_m = n, r <= sum_{t=1}^{m} ( (sum_{q=0}^{p_t-1} nums[q]) + k*t ) * (sum_{q=p_{t-1}}^{p_t-1} cost[q]).
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000. -/
  theorem spec_6 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        ∀ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m → IsCutSeq nums.val.length m p →
          r.val ≤ divCost (vals nums) (vals cost) k.val m p := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          ∀ (m : ℕ) (p : ℕ → ℕ), 1 ≤ m → IsCutSeq nums.val.length m p →
            r.val ≤ divCost (vals nums) (vals cost) k.val m p) := by
    sorry

  /-- Let r1 be the result of minimum_cost(nums, cost, k1) and r2 the result of minimum_cost(nums, cost, k2). Whenever both calls return results, r1 <= r2.
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; k1 and k2 are integers with 1 <= k1 <= k2 <= 1000. -/
  theorem spec_7 (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k1 k2 : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1000) :
      ∀ r1 r2 : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k1 = Aeneas.Std.Result.ok r1 →
        Aegis.MinimumCost.minimum_cost nums cost k2 = Aeneas.Std.Result.ok r2 →
        r1.val ≤ r2.val := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums cost : Aeneas.Std.Slice Aeneas.Std.I64) (k1 k2 : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk1_pos : 1 ≤ k1.val) (hk_le : k1.val ≤ k2.val) (hk2_le : k2.val ≤ 1000), ∀ r1 r2 : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k1 = Aeneas.Std.Result.ok r1 →
          Aegis.MinimumCost.minimum_cost nums cost k2 = Aeneas.Std.Result.ok r2 →
          r1.val ≤ r2.val) := by
    sorry

  /-- Let r be the result of minimum_cost(nums, cost, k) and let r' be the result of minimum_cost(nums, cost', k), where cost'[i] = c * cost[i] for every i. Whenever both calls return results, r' = c * r.
    Preconditions: n = len(nums) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000 and 1 <= cost[i] <= 1000; 1 <= k <= 1000; c is an integer with c >= 1 and c*cost[i] <= 1000 for every i. -/
  theorem spec_8 (nums cost cost' : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (c : ℤ)
      (hlen : nums.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
      (hc_pos : 1 ≤ c) (hc_le : ∀ y ∈ vals cost, c * y ≤ 1000)
      (hcost' : vals cost' = (vals cost).map (fun y => c * y)) :
      ∀ r r' : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        Aegis.MinimumCost.minimum_cost nums cost' k = Aeneas.Std.Result.ok r' →
        r'.val = c * r.val := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums cost cost' : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (c : ℤ)
        (hlen : nums.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000)
        (hc_pos : 1 ≤ c) (hc_le : ∀ y ∈ vals cost, c * y ≤ 1000)
        (hcost' : vals cost' = (vals cost).map (fun y => c * y)), ∀ r r' : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          Aegis.MinimumCost.minimum_cost nums cost' k = Aeneas.Std.Result.ok r' →
          r'.val = c * r.val) := by
    sorry

  /-- Let r = minimum_cost(nums, cost, k) and r2 = minimum_cost(nums, cost2, k). Whenever both calls return results, r <= r2.
    Preconditions: n = len(nums) = len(cost) = len(cost2); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000, 1 <= cost[i] <= 1000, 1 <= cost2[i] <= 1000, and cost[i] <= cost2[i]; 1 <= k <= 1000. -/
  theorem spec_9 (nums cost cost2 : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hlen2 : nums.val.length = cost2.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost2 : ∀ x ∈ cost2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hle : List.Forall₂ (· ≤ ·) (vals cost) (vals cost2))
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r r2 : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        Aegis.MinimumCost.minimum_cost nums cost2 k = Aeneas.Std.Result.ok r2 →
        r.val ≤ r2.val := by
    sorry

  theorem spec_9_neg :
      ¬ (∀ (nums cost cost2 : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hlen2 : nums.val.length = cost2.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost2 : ∀ x ∈ cost2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hle : List.Forall₂ (· ≤ ·) (vals cost) (vals cost2))
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r r2 : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          Aegis.MinimumCost.minimum_cost nums cost2 k = Aeneas.Std.Result.ok r2 →
          r.val ≤ r2.val) := by
    sorry

  /-- Let r = minimum_cost(nums, cost, k) and r2 = minimum_cost(nums2, cost, k). Whenever both calls return results, r <= r2.
    Preconditions: n = len(nums) = len(nums2) = len(cost); 1 <= n <= 1000; for every i with 0 <= i < n, 1 <= nums[i] <= 1000, 1 <= nums2[i] <= 1000, 1 <= cost[i] <= 1000, and nums[i] <= nums2[i]; 1 <= k <= 1000. -/
  theorem spec_10 (nums nums2 cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
      (hlen : nums.val.length = cost.val.length)
      (hlen2 : nums2.val.length = cost.val.length)
      (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
      (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hnums2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
      (hle : List.Forall₂ (· ≤ ·) (vals nums) (vals nums2))
      (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000) :
      ∀ r r2 : Aeneas.Std.I64,
        Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
        Aegis.MinimumCost.minimum_cost nums2 cost k = Aeneas.Std.Result.ok r2 →
        r.val ≤ r2.val := by
    sorry

  theorem spec_10_neg :
      ¬ (∀ (nums nums2 cost : Aeneas.Std.Slice Aeneas.Std.I64) (k : Aeneas.Std.I64)
        (hlen : nums.val.length = cost.val.length)
        (hlen2 : nums2.val.length = cost.val.length)
        (hn_pos : 1 ≤ nums.val.length) (hn_le : nums.val.length ≤ 1000)
        (hnums : ∀ x ∈ nums.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hnums2 : ∀ x ∈ nums2.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hcost : ∀ x ∈ cost.val, 1 ≤ x.val ∧ x.val ≤ 1000)
        (hle : List.Forall₂ (· ≤ ·) (vals nums) (vals nums2))
        (hk_pos : 1 ≤ k.val) (hk_le : k.val ≤ 1000), ∀ r r2 : Aeneas.Std.I64,
          Aegis.MinimumCost.minimum_cost nums cost k = Aeneas.Std.Result.ok r →
          Aegis.MinimumCost.minimum_cost nums2 cost k = Aeneas.Std.Result.ok r2 →
          r.val ≤ r2.val) := by
    sorry

  end AegisSpec.MinimumCost
