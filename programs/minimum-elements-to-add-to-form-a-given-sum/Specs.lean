import Aegis.MinElements.Code.Funs

/-!
# Specifications of `Aegis.MinElements.min_elements`

LeetCode problem `minimum-elements-to-add-to-form-a-given-sum`. Each `spec_<n>` theorem states one property of the function.
-/

open Aeneas Aeneas.Std Result

  namespace AegisSpec.MinElements

  def total (nums : Slice Std.I64) : ℤ := (nums.val.map (fun x => x.val)).sum

  def deficit (nums : Slice Std.I64) (goal : Std.I64) : ℤ := goal.val - total nums

  def deficitAbs (nums : Slice Std.I64) (goal : Std.I64) : ℤ := (deficit nums goal).natAbs

  def requiredSteps (nums : Slice Std.I64) (limit goal : Std.I64) : ℤ :=
    (deficitAbs nums goal + limit.val - 1) / limit.val

  def HasWitness (k lo hi s : ℤ) : Prop :=
    ∃ js : List ℤ, (js.length : ℤ) = k ∧ (∀ a ∈ js, lo ≤ a ∧ a ≤ hi) ∧ js.sum = s

  /-- Whenever the function returns a result r, r is the least nonnegative integer k such that |D| <= k * limit. Equivalently, r = ceil(|D| / limit), with ceil(0 / limit) = 0. Thus r is the minimum number of added integers, each in [-limit, limit], needed to make the total sum equal to goal.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_1 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      (0 ≤ r.val ∧
        deficitAbs nums goal ≤ r.val * limit.val ∧
        (∀ k : ℤ, 0 ≤ k → deficitAbs nums goal ≤ k * limit.val → r.val ≤ k)) ∧
      r.val = requiredSteps nums limit goal := by
    sorry

  theorem spec_1_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), (0 ≤ r.val ∧
          deficitAbs nums goal ≤ r.val * limit.val ∧
          (∀ k : ℤ, 0 ≤ k → deficitAbs nums goal ≤ k * limit.val → r.val ≤ k)) ∧
        r.val = requiredSteps nums limit goal) := by
    sorry

  /-- The function returns a result r (it does not fail, overflow, panic, or access memory out of bounds) for every input satisfying the preconditions.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_2 (nums : Slice Std.I64) (limit goal : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9) :
      ∃ r : Std.I64, Aegis.MinElements.min_elements nums limit goal = Result.ok r := by
    sorry

  theorem spec_2_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9), ∃ r : Std.I64, Aegis.MinElements.min_elements nums limit goal = Result.ok r) := by
    sorry

  /-- Whenever the function returns a result r, r <= |D|.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_3 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      r.val ≤ deficitAbs nums goal := by
    sorry

  theorem spec_3_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), r.val ≤ deficitAbs nums goal) := by
    sorry

  /-- Whenever the function returns a result r, |D| <= r * limit.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_4 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      deficitAbs nums goal ≤ r.val * limit.val := by
    sorry

  theorem spec_4_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), deficitAbs nums goal ≤ r.val * limit.val) := by
    sorry

  /-- Whenever the function returns a result r, if r > 0 then (r - 1) * limit < |D|. Equivalently, no nonnegative integer k with k < r satisfies |D| <= k * limit.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_5 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      (0 < r.val → (r.val - 1) * limit.val < deficitAbs nums goal) ∧
      (∀ k : ℤ, 0 ≤ k → k < r.val → ¬ deficitAbs nums goal ≤ k * limit.val) := by
    sorry

  theorem spec_5_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), (0 < r.val → (r.val - 1) * limit.val < deficitAbs nums goal) ∧
        (∀ k : ℤ, 0 ≤ k → k < r.val → ¬ deficitAbs nums goal ≤ k * limit.val)) := by
    sorry

  /-- Whenever the function returns a result r, there exist r integers a_0, ..., a_{r-1} such that for every j with 0 <= j < r, -limit <= a_j <= limit, and S + sum_{j=0}^{r-1} a_j = goal. (For r = 0 the sum over j is the empty sum 0.)
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_6 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      HasWitness r.val (-limit.val) limit.val (deficit nums goal) := by
    sorry

  theorem spec_6_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), HasWitness r.val (-limit.val) limit.val (deficit nums goal)) := by
    sorry

  /-- Whenever the function returns a result r, the following holds: if D > 0 then there exist r integers a_0, ..., a_{r-1} with 0 <= a_j <= limit for all j < r and sum_{j=0}^{r-1} a_j = D; if D < 0 then there exist r integers a_0, ..., a_{r-1} with -limit <= a_j <= 0 for all j < r and sum_{j=0}^{r-1} a_j = D; if D = 0 then r = 0.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_7 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      (0 < deficit nums goal → HasWitness r.val 0 limit.val (deficit nums goal)) ∧
      (deficit nums goal < 0 →
        HasWitness r.val (-limit.val) 0 (deficit nums goal)) ∧
      (deficit nums goal = 0 → r.val = 0) := by
    sorry

  theorem spec_7_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), (0 < deficit nums goal → HasWitness r.val 0 limit.val (deficit nums goal)) ∧
        (deficit nums goal < 0 →
          HasWitness r.val (-limit.val) 0 (deficit nums goal)) ∧
        (deficit nums goal = 0 → r.val = 0)) := by
    sorry

  /-- Whenever the function returns a result r for (nums, limit, goal), for every slice nums' satisfying the same constraints (length between 1 and 100000, entries between -limit and limit) and having total sum sum_{i=0}^{len(nums')-1} nums'[i] equal to S, the call min_elements(nums', limit, goal) returns the same result r.
    Preconditions: len(nums) is an integer with 1 <= len(nums) <= 100000; 1 <= limit <= 1000000; for every i with 0 <= i < len(nums), -limit <= nums[i] <= limit; -10^9 <= goal <= 10^9. All values are 64-bit signed integers, and under these bounds the mathematical sum S = sum_{i=0}^{len(nums)-1} nums[i] and D = goal - S lie in the 64-bit signed range. -/
  theorem spec_8 (nums : Slice Std.I64) (limit goal r : Std.I64)
      (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
      (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
      (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
      (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
      (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r) :
      ∀ nums' : Slice Std.I64,
        1 ≤ nums'.val.length →
        nums'.val.length ≤ 100000 →
        (∀ x ∈ nums'.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val) →
        total nums' = total nums →
        Aegis.MinElements.min_elements nums' limit goal = Result.ok r := by
    sorry

  theorem spec_8_neg :
      ¬ (∀ (nums : Slice Std.I64) (limit goal r : Std.I64)
        (hlen_lo : 1 ≤ nums.val.length) (hlen_hi : nums.val.length ≤ 100000)
        (hlimit_lo : 1 ≤ limit.val) (hlimit_hi : limit.val ≤ 1000000)
        (hentries : ∀ x ∈ nums.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val)
        (hgoal_lo : -(10 : ℤ) ^ 9 ≤ goal.val) (hgoal_hi : goal.val ≤ (10 : ℤ) ^ 9)
        (hres : Aegis.MinElements.min_elements nums limit goal = Result.ok r), ∀ nums' : Slice Std.I64,
          1 ≤ nums'.val.length →
          nums'.val.length ≤ 100000 →
          (∀ x ∈ nums'.val, -limit.val ≤ x.val ∧ x.val ≤ limit.val) →
          total nums' = total nums →
          Aegis.MinElements.min_elements nums' limit goal = Result.ok r) := by
    sorry

  end AegisSpec.MinElements
